/**
* @File	      : SharedMemory.h
* @Author     :
* @Description: Class implementing Shared Memory IPC functionality
*		for multiple processes communication capability.
* @See		https://cppcodetips.wordpress.com/2015/02/28/c-wrapper-class-for-shared-memory/
*/

#pragma once

#ifndef SHAREDMEMORY_H
#define SHAREDMEMORY_H

#include <string>
#include <stdio.h>
#include <semaphore.h>
#include <iostream>

// Constants and Types LINUX
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <iostream>
#include <string>
#include <unistd.h>
#include <cstring>
#include <cstdlib>
#include<cstdio>
#include <time.h>

/*
#if PLATFORM_WINDOWS
#include <windows.h>
#include <stdio.h>
#include <conio.h>
#include <tchar.h>
#endif

#if PLATFORM_LINUX
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#endif
*/

using namespace std;

/**
 *   @brief 	Shared Memory main implementation class
 */
class SharedMemory {
public:
	/* Constructor(s) - Destructor(s) */
	/**
	 *   @brief
	 *
	 */
	SharedMemory();

	/**
	 *   @brief
	 *
	 */
	SharedMemory(const string& sname);

	/**
	 *   @brief
	 *
	 */
	~SharedMemory();


	/* Process variables */
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


	/* FUNCTIONS:	Shared Memory Processing */
	/* MAIN INTERFACE */
	/**
	 * @brief		Begin using shared memory
	 */
	 void start();

	 /**
 	 * @brief		Terminate using shared memory
 	 */
 	 void stop();

	/**
	 *   @brief	Read shared memory space data
	 */
	template <typename T>
	inline T read();

	/**
	 *   @brief	Write to shared memory space data
	 */
	template <typename T>
	inline void write(T data);

	/* SUB-FUNCTIONS */
	/**
	 *   @brief	Create a new shared memory space
	 *   @param	nSize	size of shared memory space to create
	 *   @param	mode	data access mode
	 *   @return 	created successfully ?
	 */
	bool Create(size_t nSize, int mode = C_READ_WRITE);

	/**
	 *   @brief	Attach process to an existing shared memory space
	 *		    (Memory map the shared memory space data file)
	 *   @param	mode	data access mode
	 *   @return 	Attached successfully ?
	 */
	bool Attach(int mode = A_READ | A_WRITE);

	/**
	 *   @brief	Detach process from an existing shared memory space
	 *   @return 	Detached successfully ?
	 */
	bool Detach();

	/**
	 *   @brief	Lock semaphore onto shared memory space
	 *   @return 	locked successfully ?
	 */
	bool Lock();

	/**
	 *   @brief	Unlock semaphore from shared memory space
	 *   @return 	unlocked successfully ?
	 */
	bool UnLock();


	/* GETTERS */
	/**
	 *   @return 	the shared memory space ID
	 */
	int GetID() { return m_iD; }

	/**
	 *   @return 	the shared memory space ID
	 */
	sem_t* GetsemID() { return m_SemID; }

	/**
	 *   @return 	the data from the shared memory space
	 */
	void* GetData() { return m_Ptr; };

	/**
	 *   @return 	the data from the shared memory space
	 */
	const void* GetData() const { return m_Ptr; }

	/** */
	static const string sLockSemaphoreName;

	/**
	 *  @brief	Release the allocated shared memory space
	 */
	void release();

private:
	/**
	 *   @brief 	Clear shared memory space
	 */
	void clear();

	/* General */
	/** Shared Memory space name */
	string m_sName;

	/** Shared Memory space ID */
	int m_iD;

	/** Shared Memory space size */
	size_t m_nSize;

	/** Shared Memory space pointer */
	void* m_Ptr;

	/** Semaphore ID */
	sem_t* m_SemID;

	/** Default shared memory size */
	int defaultSize;

	// TEMP SM FILE
	FILE* smFile;

};

template <typename T>
inline void SharedMemory::write(T data) {
	// Lock shared memory space
	//this->Lock();

	// Write data to shared space (variable)
	char* smdata = (char*)this->GetData();
	strcpy(smdata,data);

	// Unlock shared memory space
	//this->UnLock();
}

template <typename T>
inline T SharedMemory::read() {
	// Lock shared memory space
	//this->Lock();

	// Write data to shared space (variable)
	T smdata = (char*)this->GetData();

	// Unlock shared memory space
	//this->UnLock();

	return smdata;
}

#endif // SHAREDMEMORY_H
