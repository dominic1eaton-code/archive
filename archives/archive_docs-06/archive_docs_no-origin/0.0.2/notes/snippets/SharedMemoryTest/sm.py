"""
 @File	     : SharedMemory.py
 @Author     :
 @Description: Class implementing Shared Memory IPC functionality
	       for multiple processes communication capability.
 @See	       (python implementation) https://blog.schmichael.com/2011/05/15/sharing-python-data-between-processes-using-mmap/
 @See	       (c/c++ implementation)  https://cppcodetips.wordpress.com/2015/02/28/c-wrapper-class-for-shared-memory/
"""

# Imports
import ctypes
import os
import sys
import threading
import mmap

import stat

# Define file params
fname = '/testSharedmemory1'
flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL  # Refer to "man 2 open".
mode = stat.S_IRUSR | stat.S_IWUSR  # This is 0o600 in octal.
umask = 0o777 ^ mode  # Prevents always downgrading umask to 0.


def class SharedMemory():
	def __init__(self):
		self.sname = ''
		self.m_ID = ''
		self.m_semID = ''
		self.m_nSize = 0
		self.m_ptr = ''

		# Creation mode operations
		self.CREATE_MODE = ["C_READ_ONLY" : os.O_RDONLY,
			            "C_READ_WRITE": os.O_RDWR]

		# Attachment mode operations
		self.ATTACH_MODE = ["A_READ" : mmap.PROT_READ,
			       	    "A_WRITE": mmap.PROT_WRITE]

		# Open the semaphore
		self.m_SemID = os.open('/tmp/mmaptest', os.O_CREAT | os.O_TRUNC | os.O_RDWR)

	# OPERATIONS
	# @brief	create a new shared memory space
	# @param	nSize	size of the newly created space
	# @param 	mode	data access mode
	def create(self, nSize, mode=self.CREATE_MODE["C_READ_ONLY"]):
		self.m_nSize = nSize;
		return None

	# @brief	attach process to an existing shared memory space
	# @param 	mode	data access mode
	def attach(self, mode):
		return None

	# @brief	detach process from an existing shared memory space
	def detach(self):
		return None

	# @brief	lock onto (reserve) a shared memory space
	def lock(self):
		return None

	# @brief	unlock from (unreserve) a shared memory space
	def unlock(self):
		return None

	# @brief	read the shared memory space
	def read(self):
		return None

	# @brief	write to the shared memory space
	def write(self):
		return None

	# @brief	release shared memory space
	def release(self):
		return None

	# @brief	clear (remove) an existing shared memory space
	def clear(self):
		return None

	# GETTERS
	# Get shared memory space ID
	def getID(self):
		return self.m_ID

	# Get shared memory space data pointer
	def getData(self):
		return self.m_ptr
