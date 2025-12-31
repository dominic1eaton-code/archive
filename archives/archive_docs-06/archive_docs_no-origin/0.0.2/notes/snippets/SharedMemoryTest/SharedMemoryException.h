/**
* @File	      : SharedMemoryException.h
* @Author     :	
* @Description: Class implementing Shared Memory IPC exception handling
*		functionality. 
* @See		https://cppcodetips.wordpress.com/2015/02/28/c-wrapper-class-for-shared-memory/
*/

#pragma once

#ifndef SHAREDMEMORYEXCEPTION_H
#define SHAREDMEMORYEXCEPTION_H

#include <string>

using namespace std;


/**
 *   @brief 	Shared Memory exception handler class 
 */
class SharedMemoryException : public std::exception {
public:
	SharedMemoryException();

	/**  @brief	Construct a SharedMemoryException with a explanatory message.
	 *   @param 	message 	explanatory message
   	 *   @param 	bSysMsg 	true if system message (from strerror(errno))
   	 *   @note	should be postfixed to the user provided message 
	 */
	SharedMemoryException(const string &message, bool bSysMsg = false) throw();

	/** */
	~SharedMemoryException() throw();

	/** @brief	Returns a pointer to the (constant) error description.
	*   @return 	A pointer to a \c const \c char*. The underlying memory
	*          	is in posession of the \c Exception object. Callers \a must
	*          	not attempt to free the memory.
	*/
	virtual const char* what() const throw (){  return m_sMsg.c_str(); }

protected:
	/** Size of memory shared */
	std::string m_sMsg;
};

#endif // SHAREDMEMORYEXCEPTION_H
