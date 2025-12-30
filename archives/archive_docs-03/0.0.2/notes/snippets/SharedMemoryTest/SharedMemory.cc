/**
* @File	      : SharedMemory.cc
* @Author     :
* @Description: Class implementing Shared Memory IPC functionality
*		for multiple processes communication capability.
*
*/


// Includes
#include "SharedMemory.h"
#include "SharedMemoryException.h"

#include <sys/mman.h>
#include <errno.h>
#include <cstdio>
#include <cstdlib>
#include <unistd.h>

const string SharedMemory::sLockSemaphoreName = "/semaphoreInit";

SharedMemory::SharedMemory() {
	m_nSize = defaultSize;
}

SharedMemory::SharedMemory(const string& sName)
	:	m_sName(sName),
		m_Ptr(NULL),
		m_iD(-1),
   	m_SemID(NULL),
		m_nSize(0)
{
	// Open the semaphore
	m_SemID = sem_open(sLockSemaphoreName.c_str(), O_CREAT, S_IRUSR | S_IWUSR, 1);

	//char *y = new char[sName.length() + 1];
	//strcpy(y, sName.c_str());
	smFile = fopen(sName.c_str(),"w+");

	m_nSize = defaultSize;
}


SharedMemory::~SharedMemory() {
	//clear();
}

void SharedMemory::start() {
	// Create()
	// Attach()
}

void SharedMemory::stop() {
	// Release()
}

bool SharedMemory::Create(size_t nSize, int mode /*= READ_WRITE*/) {
	m_nSize = nSize;
	printf("Creating shared memory \n");
	m_iD = shm_open(m_sName.c_str(), O_CREAT | mode, S_IRWXU | S_IRWXG);

	// Exception Handling
	if(m_iD < 0) {
		switch(errno) {
			case EACCES:
				printf("Permission Exception -- ");
				throw SharedMemoryException("Permission Exception -- ");
				break;
			case EEXIST:
				printf("Shared memory object specified by name already exists.");
				throw SharedMemoryException("Shared memory object specified by name already exists.");
				break;
			case EINVAL:
				printf("Invalid shared memory name passed.");
				throw SharedMemoryException("Invalid shared memory name passed.");
				break;
			case EMFILE:
				printf("The process already has the maximum number of files open.");
				throw SharedMemoryException("The process already has the maximum number of files open.");
				break;
			case ENAMETOOLONG:
				printf("The length of name exceeds PATH_MAX.");
				throw SharedMemoryException("The length of name exceeds PATH_MAX.");
				break;
			case ENFILE:
				printf("The limit on the total number of files open on the system has been reached");
				throw SharedMemoryException("The limit on the total number of files open on the system has been reached");
				break;
			default:
				printf("Invalid exception occurred in shared memory creation");
				throw SharedMemoryException("Invalid exception occurred in shared memory creation");
			break;
		}
	}

	// adjusting mapped file size (make room for the whole segment to map)      --  ftruncate()
	ftruncate(m_iD, m_nSize);

	// Attach to mapped memory file
	//Attach();

	return true;
}

bool SharedMemory::Attach( int mode /*= A_READ | A_WRITE*/ )
{
	// requesting the shared segment    --  mmap()
	m_Ptr = mmap(NULL, m_nSize, mode, MAP_SHARED, m_iD, 0);
	//m_Ptr = mmap(NULL, m_nSize, mode, MAP_SHARED, smFile, 0);

	if (m_Ptr == NULL) {
		throw SharedMemoryException("Exception in attaching the shared memory region");
	}
	return true;
}

bool SharedMemory::Detach()
{
   munmap(m_Ptr, m_nSize);
}

bool SharedMemory::Lock()
{
   sem_wait(m_SemID);
}

bool SharedMemory::UnLock()
{
   sem_post(m_SemID);
}

void SharedMemory::release() {
	// detach from mapped memory file
	Detach
	
	// Release shared memory space
	if(m_iD != -1) {
		if ( shm_unlink(m_sName.c_str()) < 0 ) {
			perror("shm_unlink");
		}
	}

	// unlink: Remove a named semaphore  from the system.
	if(m_SemID != NULL) {
		// Semaphore Close: Close a named semaphore
		if ( sem_close(m_SemID) < 0 ) {
			perror("sem_close");
		}
		// Semaphore unlink: Remove a named semaphore  from the system.
		if ( sem_unlink(sLockSemaphoreName.c_str()) < 0 ) {
			perror("sem_unlink");
		}
	}
}


void SharedMemory::clear() {
	if(m_iD != -1) {
		if ( shm_unlink(m_sName.c_str()) < 0 ) {
			perror("shm_unlink");
		}
	}

	// unlink: Remove a named semaphore  from the system.
	if(m_SemID != NULL) {
		// Semaphore Close: Close a named semaphore
		if ( sem_close(m_SemID) < 0 ) {
			perror("sem_close");
		}
		// Semaphore unlink: Remove a named semaphore  from the system.
		if ( sem_unlink(sLockSemaphoreName.c_str()) < 0 ) {
			perror("sem_unlink");
		}
	}
}
