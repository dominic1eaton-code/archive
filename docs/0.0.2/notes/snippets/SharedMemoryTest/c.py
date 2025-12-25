import mmap
import os
import struct
import time
import random
import ctypes

def main():
	maxWrites = 10
	fname = '/testSharedmemory1'

	# Open the file for reading
	fd = os.open(fname, os.O_RDONLY)

	# Memory map the file
	buf = mmap.mmap(fd, mmap.PAGESIZE, mmap.MAP_SHARED, mmap.PROT_READ)


	
	# Open the file for reading
	fd = os.open(fname, os.O_WRONLY)

	# Memory map the file
	buf = mmap.mmap(fd, mmap.PAGESIZE, mmap.MAP_SHARED, mmap.PROT_READ)

	i = None
	s = None


	for i in range(maxWrites):
		# Now create an int in the memory mapping
		i = ctypes.c_int.from_buffer(buf)

		# Set a value
		i.value = random.randint(0, 100)

		## And manipulate it for kicks
		#i.value += 1

		assert i.value == 11

		# Before we create a new value, we need to find the offset of the next free
		# memory address within the mmap
		offset = struct.calcsize(i._type_)

		# The offset should be uninitialized ('\x00')
		assert buf[offset] == '\x00'

		# Now ceate a string containing 'foo' by first creating a c_char array
		s_type = ctypes.c_char * len('foo')

		# Now create the ctypes instance
		s = s_type.from_buffer(buf, offset)

		# And finally set it
		s.raw = 'foo'

		print 'First 10 bytes of memory mapping: %r' % buf[:10]
		raw_input('Now run b.py and press ENTER')

		print
		print 'Changing i'
		i.value *= i.value

		print 'Changing s'
		s.raw = 'bar'

		new_i = raw_input('Enter a new value for i: ')
		i.value = int(new_i)
		time.sleep(1)


if __name__ == '__main__':
	main()
