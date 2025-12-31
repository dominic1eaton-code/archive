/**
* @File	      : testSM_2.cc
* @Author     :	
* @Description: test Shared Memory IPC functionality.
*		
*/


// Includes 
#include "SharedMemory.h"
/*
#include <boost/interprocess/shared_memory_object.hpp>
#include <stdio.h>
#include <time.h> 

main (void)
{

	SharedMemory* sm = new SharedMemory();

	printf ("Hello, world!\n");
	return 0;
}
*/

#include "SharedMemory.h"
#include <iostream>
#include <string>
#include <unistd.h>
#include <cstring>
#include <cstdlib>
#include<cstdio>
#include <time.h> 

using namespace std;
int main(int argc, char* argv[]) {
	printf("**SHARED MEMORY TEST** \n");
	const char *loggingStr = "Logging: ";
 	int maxWrites = 5;
	int maxReads = 30;
	int memSize = 100; 
	srand (time(NULL));
	int pId = rand() % 1000;


	try {

		printf("%i %s attempting to create Shared Memory space \n", pId, loggingStr);

		//SharedMemory* shmMemory = new SharedMemory("/testSharedmemory1");
		//shmMemory->Create(memSize);
		//shmMemory->Attach();
		//int smID = shmMemory->GetID();	

		SharedMemory shmMemory("/testSharedmemory1");
		shmMemory.Create(memSize);
		shmMemory.Attach();
		//shmMemory.release();

		char* str = (char*)shmMemory.GetData();

		//printf("%i %s created Shared Memory space with id: %i \n", pId, loggingStr, smID);
		//char* str = (char*)shmMemory->GetData();

		if(std::string(argv[1]) =="1") {
			for(int i=0;i<maxWrites;i++)  {

				printf("%i %s locking shared memory space \n", pId, loggingStr);
				//shmMemory->Lock();
				//printf("%i %s data read from shared memory space: \n", pId, loggingStr);
				//char* readData = (char*)shmMemory->GetData();
				//cout << readData << endl;
				//shmMemory->UnLock();

				shmMemory.Lock();
				char sTemp[10];
				sprintf(sTemp,"Data:%d", rand()%100);
				cout << sTemp << endl;
				strcpy(str,sTemp);
				shmMemory.UnLock();

				sleep(2);

			}

		} else {
			for(int i=0;i<maxReads;i++)  {
				printf("%i %s attempting to read shared memory space \n", pId, loggingStr);
				char sTemp[10];
            			printf("\nReading:%d \n",i+1);
            			shmMemory.Lock();
            			printf("--->%s \n",str);
            			shmMemory.UnLock();

            			sleep(2);
			}
		}
	} catch (std::exception& ex) {
		cout<<"Exception:"<<ex.what();
	}

}
