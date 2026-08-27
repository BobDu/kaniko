/*
Copyright 2018 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package util

import (
	"crypto/md5"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math"
	"os"
	"strconv"
	"sync"
	"syscall"
	"time"

	"github.com/osscontainertools/kaniko/pkg/assert"
	"github.com/sirupsen/logrus"
	"github.com/zeebo/xxh3"
	"golang.org/x/sys/unix"
)

var ErrNotSupportedPlatform = errors.New("platform and architecture is not supported")

const (
	securityCapabilityXattr = "security.capability"
)

// hasherPrefix is the fixed-width header every hash starts with: mode, mtime seconds,
// mtime nanoseconds, uid, gid, and the length of the variable-length field that follows
// (the security capability for regular files, the target for symlinks). Fixed widths plus
// that length mean no two distinct inputs can produce the same byte stream.
//
// mtime is stored as seconds plus nanoseconds rather than UnixNano: the latter is an int64
// of nanoseconds, so it only spans 1677-2262 and silently wraps outside it, which would make
// two mtimes 584 years apart hash the same.
const hasherPrefix = 4 + 8 + 4 + 4 + 4 + 4

// Hasher returns a hash function, used in snapshotting to determine if a file has changed
func Hasher() func(string) (string, error) {
	bufs := sync.Pool{
		New: func() any {
			// 320 KiB, unchanged (was highwayhash.Size*10*1024).
			b := make([]byte, 320*1024)
			return &b
		},
	}
	// Only a file that does not fit in one buffer needs the streaming hasher; everything
	// else is hashed in one call below, which needs no hasher state at all.
	hashers := sync.Pool{New: func() any { return xxh3.New() }}

	// streamRest hashes the header already sitting in buf, then the rest of f.
	streamRest := func(buf []byte, upto int, f io.Reader) (string, error) {
		h := hashers.Get().(*xxh3.Hasher)
		h.Reset()
		defer hashers.Put(h)
		h.Write(buf[:upto])
		if _, err := io.CopyBuffer(h, f, buf); err != nil {
			return "", err
		}
		return hex.EncodeToString(h.Sum(nil)), nil
	}

	hasher := func(p string) (string, error) {
		fi, err := os.Lstat(p)
		if err != nil {
			return "", err
		}

		bufp := bufs.Get().(*[]byte)
		defer bufs.Put(bufp)
		buf := *bufp

		st := fi.Sys().(*syscall.Stat_t)
		mtime := fi.ModTime()
		binary.LittleEndian.PutUint32(buf[0:], uint32(fi.Mode()))
		binary.LittleEndian.PutUint64(buf[4:], uint64(mtime.Unix()))
		binary.LittleEndian.PutUint32(buf[12:], uint32(mtime.Nanosecond()))
		binary.LittleEndian.PutUint32(buf[16:], st.Uid)
		binary.LittleEndian.PutUint32(buf[20:], st.Gid)
		binary.LittleEndian.PutUint32(buf[24:], 0)
		n := hasherPrefix

		switch {
		case fi.Mode().IsRegular():
			capability, _ := Lgetxattr(p, "security.capability")
			// Guarded rather than a bare Assert: this runs per file, and Assert's variadic
			// arguments are boxed at the call site even when the condition holds.
			if hasherPrefix+len(capability) > len(buf) {
				assert.Assert("hasher.capability-fits", false,
					"security.capability of %s is %d bytes, larger than the %d byte hash buffer", p, len(capability), len(buf))
			}
			binary.LittleEndian.PutUint32(buf[24:], uint32(len(capability)))
			n += copy(buf[n:], capability)

			f, err := FSys.Open(p)
			if err != nil {
				return "", err
			}
			defer f.Close()

			// Streaming a file that clearly does not fit avoids reading a whole
			// buffer for nothing. Size is only a hint: if it understates, ReadFull
			// below fills the buffer and falls through to streaming anyway.
			if fi.Size() > int64(len(buf)-n) {
				return streamRest(buf, n, f)
			}

			read, err := io.ReadFull(f, buf[n:])
			switch err {
			case io.EOF, io.ErrUnexpectedEOF:
				// The whole file fit alongside the header.
				n += read
			case nil:
				// More to read than Size claimed: xxh3 gives the same digest either way.
				return streamRest(buf, n+read, f)
			default:
				return "", err
			}
		case fi.Mode()&os.ModeSymlink == os.ModeSymlink:
			linkPath, err := os.Readlink(p)
			if err != nil {
				return "", err
			}
			if hasherPrefix+len(linkPath) > len(buf) {
				assert.Assert("hasher.linkpath-fits", false,
					"symlink target of %s is %d bytes, larger than the %d byte hash buffer", p, len(linkPath), len(buf))
			}
			binary.LittleEndian.PutUint32(buf[24:], uint32(len(linkPath)))
			n += copy(buf[n:], linkPath)
		}

		var sum [8]byte
		binary.BigEndian.PutUint64(sum[:], xxh3.Hash(buf[:n]))
		return hex.EncodeToString(sum[:]), nil
	}
	return hasher
}

// CacheHasher takes into account everything the regular hasher does except for mtime
func CacheHasher() func(string) (string, error) {
	hasher := func(p string) (string, error) {
		h := md5.New()
		fi, err := os.Lstat(p)
		if err != nil {
			return "", err
		}
		h.Write([]byte(fi.Mode().String()))

		h.Write([]byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Uid), 36)))
		h.Write([]byte(","))
		h.Write([]byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Gid), 36)))

		if fi.Mode().IsRegular() {
			f, err := FSys.Open(p)
			if err != nil {
				return "", err
			}
			defer f.Close()
			if _, err := io.Copy(h, f); err != nil {
				return "", err
			}
		} else if fi.Mode()&os.ModeSymlink == os.ModeSymlink {
			linkPath, err := os.Readlink(p)
			if err != nil {
				return "", err
			}
			h.Write([]byte(linkPath))
		}

		return hex.EncodeToString(h.Sum(nil)), nil
	}
	return hasher
}

// MtimeHasher returns a hash function, which only looks at mtime to determine if a file has changed.
// Note that the mtime can lag, so it's possible that a file will have changed but the mtime may look the same.
func MtimeHasher() func(string) (string, error) {
	hasher := func(p string) (string, error) {
		h := md5.New()
		fi, err := os.Lstat(p)
		if err != nil {
			return "", err
		}
		h.Write([]byte(fi.ModTime().String()))
		return hex.EncodeToString(h.Sum(nil)), nil
	}
	return hasher
}

// RedoHasher returns a hash function, which looks at mtime, size, filemode, owner uid and gid
// Note that the mtime can lag, so it's possible that a file will have changed but the mtime may look the same.
func RedoHasher() func(string) (string, error) {
	hasher := func(p string) (string, error) {
		h := md5.New()
		fi, err := os.Lstat(p)
		if err != nil {
			return "", err
		}

		if logrus.IsLevelEnabled(logrus.DebugLevel) {
			logrus.Debugf("Hash components for file: %s, mode: %s, mtime: %s, size: %s, user-id: %s, group-id: %s",
				p, []byte(fi.Mode().String()), []byte(fi.ModTime().String()),
				[]byte(strconv.FormatInt(fi.Size(), 16)), []byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Uid), 36)),
				[]byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Gid), 36)))
		}

		h.Write([]byte(fi.Mode().String()))
		h.Write([]byte(fi.ModTime().String()))
		h.Write([]byte(strconv.FormatInt(fi.Size(), 16)))
		h.Write([]byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Uid), 36)))
		h.Write([]byte(","))
		h.Write([]byte(strconv.FormatUint(uint64(fi.Sys().(*syscall.Stat_t).Gid), 36)))

		return hex.EncodeToString(h.Sum(nil)), nil
	}
	return hasher
}

// SHA256 returns the shasum of the contents of r
func SHA256(r io.Reader) (string, error) {
	hasher := sha256.New()
	_, err := io.Copy(hasher, r)
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(hasher.Sum(make([]byte, 0, hasher.Size()))), nil
}

type retryFunc func() error

// Retry retries an operation
func Retry(operation retryFunc, retryCount int, initialDelayMilliseconds int) error {
	err := operation()
	for i := 0; err != nil && i < retryCount; i++ {
		sleepDuration := time.Millisecond * time.Duration(int(math.Pow(2, float64(i)))*initialDelayMilliseconds)
		logrus.Warnf("Retrying operation after %s due to %v", sleepDuration, err)
		time.Sleep(sleepDuration)
		err = operation()
	}

	return err
}

// Retry retries an operation with a return value
func RetryWithResult[T any](operation func() (T, error), retryCount int, initialDelayMilliseconds int) (result T, err error) {
	result, err = operation()
	if err == nil {
		return result, nil
	}
	for i := range retryCount {
		sleepDuration := time.Millisecond * time.Duration(int(math.Pow(2, float64(i)))*initialDelayMilliseconds)
		logrus.Warnf("Retrying operation after %s due to %v", sleepDuration, err)
		time.Sleep(sleepDuration)

		result, err = operation()
		if err == nil {
			return result, nil
		}
	}

	return result, fmt.Errorf("unable to complete operation after %d attempts, last error: %w", retryCount, err)
}

func Lgetxattr(path string, attr string) ([]byte, error) {
	// Start with a 128 length byte array
	dest := make([]byte, 128)
	sz, errno := unix.Lgetxattr(path, attr, dest)

	for errors.Is(errno, unix.ERANGE) {
		// Buffer too small, use zero-sized buffer to get the actual size
		sz, errno = unix.Lgetxattr(path, attr, []byte{})
		if errno != nil {
			return nil, errno
		}
		dest = make([]byte, sz)
		sz, errno = unix.Lgetxattr(path, attr, dest)
	}

	switch {
	case errors.Is(errno, unix.ENODATA),
		errors.Is(errno, syscall.EOPNOTSUPP),
		errors.Is(errno, ErrNotSupportedPlatform):
		return nil, nil
	case errno != nil:
		return nil, errno
	}

	return dest[:sz], nil
}

func Lsetxattr(path string, attr string, data []byte, flags int) error {
	return unix.Lsetxattr(path, attr, data, flags)
}
