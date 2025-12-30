#include "SharedMemory.h"
#include <iostream>
#include <string>
#include <unistd.h>
#include <cstring>
#include <cstdlib>
#include<cstdio>
#include <time.h> 


using namespace std;

const string sLockSemaphoreName = "/semaphoreInit";


int main(int argc, char* argv[]) {
	printf("**SHARED MEMORY TEST** \n");
	const char *loggingStr = "Logging: ";
 	int maxWrites = 10;
	int maxReads = 40;
	int memSize = 100; 
	int sSize = 10;
	srand (time(NULL));
	int pId = rand() % 1000;
	string fname = "/testSharedmemory1";



	// TESTING 
	try {
		// Create sm 
		SharedMemory* shmMemory = new SharedMemory("/testSharedmemory1");
		shmMemory->Create(memSize);
		char* str = (char*)shmMemory->GetData();
		int rVal;
		string sData; 

		// WRITE to sm 
		if(std::string(argv[1]) =="1") {
			for(int i=0;i<maxWrites;i++)  {
				printf("%i %s attempting to write to shared memory space \n", pId, loggingStr);
	
				rVal = rand()%memSize-1;
				sData = std::to_string(rVal);
				//sprintf(sTemp, sizeof(sTemp)/sizeof(sTemp[0]), "Data:%d", rand()%memSize-1);
				cout << pId << " " << loggingStr << sData << endl;
				printf("%i %s nData: %d\n", pId, loggingStr, sData.c_str());
				printf("%i %s rData: %d\n", pId, loggingStr, rVal);
				shmMemory->write(sData.c_str());

				sleep(2);
			}

		// READ from sm 
		} else if(std::string(argv[1]) =="2")  {
			for(int i=0;i<maxReads;i++)  {
				printf("%i %s attempting to read from shared memory space \n", pId, loggingStr);
				sData = shmMemory->read<string>();
				cout << pId << " " << loggingStr << sData << endl;

				sleep(2);
			}
		}

		// Release sm
		shmMemory->release();
	} catch (std::exception& ex) {
		cout<<"Exception:"<<ex.what();
	}
}
