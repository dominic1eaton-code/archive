#include <string>
#include <stdio.h>
#include <semaphore.h>

#include <iostream>
#include <string>
#include <unistd.h>
#include <cstring>
#include <cstdlib>
#include<cstdio>
#include <time.h> 

#include <errno.h>


// Constants and Types 
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>


using namespace std;

const string sLockSemaphoreName = "/semaphoreInit";


int main(int argc, char* argv[]) {
	printf("**SHARED MEMORY TEST** \n");
	const char *loggingStr = "Logging: ";
 	int maxWrites = 3;
	int memSize = 100; 
	srand (time(NULL));
	int pId = rand() % 1000;
	string fname = "/testSharedmemory1";

	string m_sName = fname;
	size_t nSize = memSize;
	int m_iD;
	void* m_Ptr;
	sem_t* m_SemID;
	FILE* smFile; 

	enum
	{
		C_READ_ONLY  = O_RDONLY,
		C_READ_WRITE = O_RDWR,
	} CREATE_MODE;


	enum
	{
		A_READ  = PROT_READ,
		A_WRITE = PROT_WRITE,
	} ATTACH_MODE;

	
	// INIT sm 
	int m_nSize = nSize;
	string sName = m_sName;


	// Open the semaphore
	m_SemID = sem_open(sLockSemaphoreName.c_str(), O_CREAT, S_IRUSR | S_IWUSR, 1);
	
	// Open sm file
	smFile = fopen(fname.c_str(),"w+");
	
	// Create new sm 
	int mode = C_READ_WRITE;
	m_iD = shm_open(fname.c_str(), O_CREAT | mode, S_IRWXU | S_IRWXG);
	ftruncate(m_iD, memSize);

	// Attach to mm file 
	mode = A_READ | A_WRITE;
	m_Ptr = mmap(NULL, memSize, mode, MAP_SHARED, m_iD, 0);
	printf("%i Writing:  %s\n", pId, (char*)m_iD);


	// TESTING 
	// get sm data 
	char* str = (char*)m_Ptr;

	// Write to sm 
	if(std::string(argv[1]) =="1") {
		for(int i=0;i<maxWrites;i++)  {
			//char sTemp[maxWrites];
			char sDat = (char)rand()%memSize-1;

			printf("%i %s attempting to write to shared memory space \n", pId, loggingStr);

			//sprintf(sTemp,"Data:%d", rand()%memSize-1);
			//printf("%i Writing:  %s\n", pId, str);
			printf("%i %s nData: %d\n", pId, loggingStr, sDat);
	
			printf("%i %s writing to shared memory space \n", pId, loggingStr);
			// Lock sm 
			//sem_wait(m_SemID);

			// writing data
			//char* smdata = (char*)m_Ptr; // get sm data 
			//strcpy(str,(char*)sDat);

			// Unlock sm 
			//sem_post(m_SemID);

			sleep(2);
		}
	// Read from sm 
	} else if(std::string(argv[1]) =="2")  {
	
	}


	// RELEASE mmap file, sm and semaphore
	munmap(m_Ptr, m_nSize);
	shm_unlink(m_sName.c_str());

	sem_close(m_SemID);
	sem_unlink(sLockSemaphoreName.c_str());
}
