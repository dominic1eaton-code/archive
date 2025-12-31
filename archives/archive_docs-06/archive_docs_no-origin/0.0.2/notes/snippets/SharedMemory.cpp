/**
* File		 : SharedMemory.cpp
* Description:
* NOTE		 :
*/

/*----------------------------------------------------
		Includes
----------------------------------------------------*/

#include "SharedMemory.h"


#if PLATFORM_WINDOWS
#include "AllowWindowsPlatformTypes.h"
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <conio.h>
#include <tchar.h>
#include <memory>
#include "HideWindowsPlatformTypes.h"
#define MUTEX_LOCK_TIMEOUT_MS 100
#endif


/*----------------------------------------------------
		Constructors
----------------------------------------------------*/

SharedMemory::SharedMemory()
	: sm_size(0)
{

}

SharedMemory::~SharedMemory()
{

}


/*----------------------------------------------------
		Operations
----------------------------------------------------*/

bool SharedMemory::CreateSharedMemory(const FString& fname, int size)
{
	return true;
}

bool SharedMemory::CreateSharedMemory(const char* name, int size)
{
	return true;
}

//bool SharedMemory::WriteShared(const void* data, int size, int offset = 0)
//{
//	return true;
//}
//
//bool SharedMemory::ReadShared(void* data, int size, int offset = 0)
//{
//	return true;
//}

void SharedMemory::ReleaseSharedMemory()
{
	
}

bool SharedMemory::IsOpen()
{
	return true;
}


/*----------------------------------------------------
		Windows
----------------------------------------------------*/

#if PLATFORM_WINDOWS

bool SharedMemory::LockMutex()
{
	return true;
}

void SharedMemory::UnlockMutex()
{

}

#endif