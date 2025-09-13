package fusefs

import (
	"context"
	"os"
	"path"
	"time"

	"bazil.org/fuse"
	"bazil.org/fuse/fs"
	"github.com/containerd/containerd/log"
	"github.com/containerd/containerd/snapshots/storage"
	"github.com/opencontainers/go-digest"

	"github.com/hologram/hologram-snapshotter/pkg/content"
)

// Root represents the root directory of a FUSE filesystem
type Root struct {
	fs       *Filesystem
	snapshot storage.Snapshot
	content  *content.Store
	ctx      context.Context
}

// Attr returns the attributes of the root directory
func (r *Root) Attr(ctx context.Context, a *fuse.Attr) error {
	a.Inode = 1
	a.Mode = os.ModeDir | 0555
	a.Uid = 0
	a.Gid = 0
	a.Mtime = time.Now()
	a.Ctime = a.Mtime
	a.Atime = a.Mtime
	return nil
}

// Lookup looks up a file or directory in the root
func (r *Root) Lookup(ctx context.Context, name string) (fs.Node, error) {
	// For now, return a simple file system structure
	// In a real implementation, this would traverse the OCI layer structure

	// Check if it's a directory
	if name == "bin" || name == "usr" || name == "etc" || name == "var" || name == "tmp" {
		return &Directory{
			fs:       r.fs,
			snapshot: r.snapshot,
			content:  r.content,
			ctx:      r.ctx,
			path:     "/" + name,
		}, nil
	}

	// Check if it's a file
	if name == "hello.txt" || name == "README.md" {
		return &File{
			fs:       r.fs,
			snapshot: r.snapshot,
			content:  r.content,
			ctx:      r.ctx,
			path:     "/" + name,
		}, nil
	}

	return nil, fuse.ENOENT
}

// ReadDirAll reads all entries in the root directory
func (r *Root) ReadDirAll(ctx context.Context) ([]fuse.Dirent, error) {
	// Return a basic directory structure
	// In a real implementation, this would read from the OCI layer manifest
	return []fuse.Dirent{
		{Inode: 2, Name: "bin", Type: fuse.DT_Dir},
		{Inode: 3, Name: "usr", Type: fuse.DT_Dir},
		{Inode: 4, Name: "etc", Type: fuse.DT_Dir},
		{Inode: 5, Name: "var", Type: fuse.DT_Dir},
		{Inode: 6, Name: "tmp", Type: fuse.DT_Dir},
		{Inode: 7, Name: "hello.txt", Type: fuse.DT_File},
		{Inode: 8, Name: "README.md", Type: fuse.DT_File},
	}, nil
}

// Directory represents a directory in the FUSE filesystem
type Directory struct {
	fs       *Filesystem
	snapshot storage.Snapshot
	content  *content.Store
	ctx      context.Context
	path     string
}

// Attr returns the attributes of the directory
func (d *Directory) Attr(ctx context.Context, a *fuse.Attr) error {
	a.Inode = digest.FromString(d.path).String()
	a.Mode = os.ModeDir | 0555
	a.Uid = 0
	a.Gid = 0
	a.Mtime = time.Now()
	a.Ctime = a.Mtime
	a.Atime = a.Mtime
	return nil
}

// Lookup looks up a file or directory in this directory
func (d *Directory) Lookup(ctx context.Context, name string) (fs.Node, error) {
	childPath := path.Join(d.path, name)

	// For simplicity, return a file for any lookup
	// In a real implementation, this would check the actual layer structure
	return &File{
		fs:       d.fs,
		snapshot: d.snapshot,
		content:  d.content,
		ctx:      d.ctx,
		path:     childPath,
	}, nil
}

// ReadDirAll reads all entries in the directory
func (d *Directory) ReadDirAll(ctx context.Context) ([]fuse.Dirent, error) {
	// Return empty directory for now
	// In a real implementation, this would read from the OCI layer
	return []fuse.Dirent{}, nil
}

// File represents a file in the FUSE filesystem
type File struct {
	fs       *Filesystem
	snapshot storage.Snapshot
	content  *content.Store
	ctx      context.Context
	path     string
}

// Attr returns the attributes of the file
func (f *File) Attr(ctx context.Context, a *fuse.Attr) error {
	// Get file info from content store
	info, err := f.content.GetFileInfo(ctx, f.snapshot.ID, f.path)
	if err != nil {
		// Return default attributes if file not found
		a.Inode = digest.FromString(f.path).String()
		a.Mode = 0444
		a.Uid = 0
		a.Gid = 0
		a.Size = 0
		a.Mtime = time.Now()
		a.Ctime = a.Mtime
		a.Atime = a.Mtime
		return nil
	}

	a.Inode = digest.FromString(f.path).String()
	a.Mode = info.Mode
	a.Uid = info.UID
	a.Gid = info.GID
	a.Size = info.Size
	a.Mtime = info.ModTime
	a.Ctime = info.ModTime
	a.Atime = info.ModTime
	return nil
}

// Read reads data from the file
func (f *File) Read(ctx context.Context, req *fuse.ReadRequest, resp *fuse.ReadResponse) error {
	start := time.Now()

	// Read data from content store
	data, err := f.content.ReadFile(ctx, f.snapshot.ID, f.path, req.Offset, req.Size)
	if err != nil {
		log.G(ctx).WithError(err).Errorf("failed to read file %s", f.path)
		return fuse.EIO
	}

	resp.Data = data

	// Update telemetry
	f.fs.telemetry.ReadOps++
	f.fs.telemetry.ReadBytes += int64(len(data))
	f.fs.telemetry.ReadLatency += time.Since(start)

	return nil
}

// Open opens the file
func (f *File) Open(ctx context.Context, req *fuse.OpenRequest, resp *fuse.OpenResponse) (fs.Handle, error) {
	// Check if file exists
	_, err := f.content.GetFileInfo(ctx, f.snapshot.ID, f.path)
	if err != nil {
		return nil, fuse.ENOENT
	}

	return f, nil
}

// ReadAll reads the entire file
func (f *File) ReadAll(ctx context.Context) ([]byte, error) {
	start := time.Now()

	data, err := f.content.ReadFile(ctx, f.snapshot.ID, f.path, 0, 0)
	if err != nil {
		return nil, err
	}

	// Update telemetry
	f.fs.telemetry.ReadOps++
	f.fs.telemetry.ReadBytes += int64(len(data))
	f.fs.telemetry.ReadLatency += time.Since(start)

	return data, nil
}

// Flush flushes any pending writes (no-op for read-only filesystem)
func (f *File) Flush(ctx context.Context, req *fuse.FlushRequest) error {
	return nil
}

// Release releases the file handle (no-op for read-only filesystem)
func (f *File) Release(ctx context.Context, req *fuse.ReleaseRequest) error {
	return nil
}
