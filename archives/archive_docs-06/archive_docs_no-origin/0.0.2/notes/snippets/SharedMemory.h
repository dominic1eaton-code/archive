/**
* File		 : SharedMemory.h
* Description: 
* NOTE		 :
*/


#pragma once


/*----------------------------------------------------
		INCLUDES
----------------------------------------------------*/

#ifndef MLR_SHAREDMEMORY_H
#define MLR_SHAREDMEMORY_H

#include <string>
#include <stdio.h>

#if PLATFORM_LINUX
#include <sys/mman.h>
#include <sys/stat.h>
#endif

/* Engine Core */
#include "CoreMinimal.h"


/*----------------------------------------------------
		CLASS DEFINITIONS
----------------------------------------------------*/

/**
 *		SharedMemory Main Class
 */
class SharedMemory
{	

private:

	/*----------------------------------------------------
			PRIVATE MEMBER METHODS
	----------------------------------------------------*/


	bool CreateSharedMemoryHelper();


	/*----------------------------------------------------
			Windows
	----------------------------------------------------*/

#if PLATFORM_WINDOWS

	bool LockMutex();
	void UnlockMutex();

	void* SharedMemoryHandle;           ///<  Mapped memory handle.
	void* SharedMemoryMutex;            ///<  Mutex handle.

#endif


	/*----------------------------------------------------
			Linux
	----------------------------------------------------*/

#if PLATFORM_LINUX

#endif


public:

	/*----------------------------------------------------
			PUBLIC MEMBER VARIABLES
	----------------------------------------------------*/
	
	/** */
	int sm_size;


public:

	/*----------------------------------------------------
			PUBLIC MEMBER METHODS
	----------------------------------------------------*/

	/*----------------------------------------------------
			Constructors
	----------------------------------------------------*/

	/** */
	SharedMemory();

	/** */
	~SharedMemory();

	/** */
	SharedMemory(const char* name, int size);

	/** */
	SharedMemory(const FString& fname, int size);


	/*----------------------------------------------------
			Operations
	----------------------------------------------------*/

	/** */
	bool CreateSharedMemory(const char* name, int size);

	/** */
	bool CreateSharedMemory(const FString& fname, int size);

	/** */
	bool WriteShared(const void* data, int size, int offset = 0);

	/** */
	bool ReadShared(void* data, int size, int offset = 0);

	/** */
	void ReleaseSharedMemory();

	/** */
	bool IsOpen();



#if PLATFORM_LINUX

	int fd;

#endif
	
	
};


#endif // MLR_SHAREDMEMORY_H
