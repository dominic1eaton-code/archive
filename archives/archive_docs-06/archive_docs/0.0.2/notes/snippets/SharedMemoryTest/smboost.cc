#include <boost/interprocess/file_mapping.hpp>
#include <boost/interprocess/shared_memory_object.hpp>
#include <boost/interprocess/mapped_region.hpp>
#include <cstring>
#include <cstdlib>
#include <string>


#include <iostream>
#include <unistd.h>
#include<cstdio>
#include <time.h> 


int main(int argc, char *argv[])
{
	using namespace boost::interprocess;

	std::string fname = "/testSharedmemory1";
	std::size_t FileSize = 100;
	int smSize = 1000;

/*
	// Create file Mapping 
	std::size_t FileSize = 100;
	file_mapping m_file("/testSharedmemory1", read_write);
	mapped_region region(m_file, read_write, FileSize/2, FileSize-FileSize/2 );

	//Get the address of the region
	region.get_address();

	//Get the size of the region
	region.get_size();
*/

	printf("**SHARED MEMORY TEST** \n");
	const char *loggingStr = "Logging: ";
	int maxWrites = 2;
	int memSize = 100; 
	srand (time(NULL));
	int pId = rand() % smSize;


	if(argc == 1) {  //Parent process
		//Remove shared memory on construction and destruction
		struct shm_remove
		{
			shm_remove() { shared_memory_object::remove("/testSharedmemory1"); }
			~shm_remove(){ shared_memory_object::remove("/testSharedmemory1"); }
		} remover;

		//Create a shared memory object.
		printf("%i %s attempting to create Shared Memory space \n", pId, loggingStr);
		shared_memory_object shm (create_only, "/testSharedmemory1", read_write);

		//Set size
		shm.truncate(smSize);

		//Map the whole shared memory in this process
		mapped_region region(shm, read_write);

		//Write all the memory to 1
		std::memset(region.get_address(), 1, region.get_size());

		//Launch child process
		std::string s(argv[0]); s += " child ";
		if(0 != std::system(s.c_str()))
		return 1;
	}
	else {
		//Open already created shared memory object.
		shared_memory_object shm (open_only, "/testSharedmemory1", read_only);

		//Map the whole shared memory in this process
		mapped_region region(shm, read_only);

		//Check that memory was initialized to 1
		char *mem = static_cast<char*>(region.get_address());
		for(std::size_t i = 0; i < region.get_size(); ++i)
		if(*mem++ != 1)
		return 1;   //Error checking memory

		// Write to shared memory space
		for(int i=0; i<maxWrites; i++) {

/*
			std::string *s = shm.construct<std::string>("String")("Hello!", shm.get_segment_manager());
			s->insert(5, ", world");
			std::cout << *s << '\n';
*/
		}

	}


	
   return 0;
}
