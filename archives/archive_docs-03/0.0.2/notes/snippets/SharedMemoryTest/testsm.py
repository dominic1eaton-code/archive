"""
	@File	    : testsm.py
	@Author	    :
	@Description:
"""

# Imports 
import multiprocessing 
import numpy as np 
from threading import Thread
from time import sleep

import ctypes
import os
import sys
import mmap 
import struct
import stat

import posix_ipc as pipc 

def threaded_function(arg):
	for i in range(arg):
		print "running"
		sleep(2)

def thread_eg():
	thread = Thread(target = threaded_function, args = (10, ))
	thread.start()
	thread.join()	

def read():
	fname = '/testSharedmemory1'
	flags = os.O_CREAT | os.O_TRUNC | os.O_RDONLY
	fd = os.open(fname, flags)
	buf = mmap.mmap(fd, mmap.PAGESIZE, mmap.MAP_SHARED, mmap.PROT_READ)

def write():
	fname = '/testSharedmemory1'
	flags = os.O_CREAT | os.O_TRUNC | os.O_WRONLY
	fd = os.open(fname, os.O_RDWR)
	#fd = os.open(fname, flags)
	assert os.write(fd, '\x00' * mmap.PAGESIZE) == mmap.PAGESIZE
	buf = mmap.mmap(fd, mmap.PAGESIZE, prot=mmap.PROT_READ|mmap.PROT_WRITE,flags=mmap.MAP_SHARED)
	i = ctypes.c_int.from_buffer(buf)
	i.value = 10
	
	print(i.value)

def main():
	"""
	fname = '/testSharedmemory1'
	flags = os.O_CREAT | os.O_TRUNC | os.O_WRONLY
	f = os.open(fname, os.O_RDWR)
	m = mmap.mmap(f, 1000000, prot=mmap.PROT_READ|mmap.PROT_WRITE,flags=mmap.MAP_SHARED)
	i = ctypes.c_int.from_buffer(buf)
	"""

	fname = '/testSharedmemory1'
	mSize = 100
	sm = pipc.SharedMemory(fname,  os.O_CREAT | os.O_RDWR, stat.S_IRWXU | stat.S_IRWXG)
	buf = mmap.mmap(sm.fd, mSize, prot=mmap.PROT_READ|mmap.PROT_WRITE,flags=mmap.MAP_SHARED)
	i = ctypes.c_int.from_buffer(buf)
	
	print(i.value)


if __name__ == '__main__':
	main()
