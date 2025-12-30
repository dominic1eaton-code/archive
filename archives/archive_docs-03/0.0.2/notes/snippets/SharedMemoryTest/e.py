
# Imports 
import multiprocessing 

import ctypes
import os
import sys
import threading
import mmap 
import struct

import stat

# Define file params
fname = '/testSharedmemory1'
#flags = os.O_CREAT | os.O_TRUNC | os.O_RDWR
flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL  # Refer to "man 2 open".
mode = stat.S_IRUSR | stat.S_IWUSR  # This is 0o600 in octal.
umask = 0o777 ^ mode  # Prevents always downgrading umask to 0.

#fd = os.open(fname)
#fd = os.open(fname, flags)
#assert os.write(fd, '\x00' * mmap.PAGESIZE) == mmap.PAGESIZE
#buf = mmap.mmap(fd, mmap.PAGESIZE, mmap.MAP_SHARED, mmap.PROT_WRITE)

def main():
	fd = os.open(fname, os.O_CREAT | os.O_TRUNC | os.O_RDWR | mode )

	# Open the file for reading
	#fd = os.open(fname, os.O_RDONLY)
	fd = os.open(fname, os.O_RDWR | os.O_TRUNC | stat.S_IRUSR | stat.S_IWUSR)
	fd = os.open(fname, os.O_RDWR | os.O_TRUNC | mode)

	# ensure Limit file size to shared memory allocation space  
	assert os.write(fd, '\x00' * mmap.PAGESIZE) == mmap.PAGESIZE

	# Memory map the file
	buf = mmap.mmap(fd, mmap.PAGESIZE, mmap.MAP_SHARED, mmap.PROT_READ)

	## PART I
	i = ctypes.c_int.from_buffer(buf)
	i.value = 10
	offset = struct.calcsize(i._type_)
	assert buf[offset] == '\x00'
	s_type = ctypes.c_char * len('foo')
	s = s_type.from_buffer(buf, offset)
	s.raw = 'foo'

	## PART II 

	i = None
	s = None

	while 1:
		new_i, = struct.unpack('i', buf[:4])
		new_s, = struct.unpack('3s', buf[4:7])

		if i != new_i or s != new_s:
			print 'i: %s => %d' % (i, new_i)
			print 's: %s => %s' % (s, new_s)
			print 'Press Ctrl-C to exit'
			i = new_i
			s = new_s

		time.sleep(2)


if __name__ == '__main__':
	main()
