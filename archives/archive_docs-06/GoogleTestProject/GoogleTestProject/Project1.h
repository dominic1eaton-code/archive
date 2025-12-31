/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */
#pragma once

#ifndef PROJECT_H
#define PROJECT_H


 // Main package name space
namespace ProjectNamespace
{
	class Project1
	{
	public:
		Project1();
		virtual ~Project1(void);

		// set internal value
		void incValue(int offset);

		// get internal value
		int getValue();

		// enable class
		void enable();

		// disable class
		void disable();

		// get enable status for class
		bool enabled();

	private: 
		// class value
		int m_value;

		// class enabled status
		bool m_enabled;
	};
} // ProjectNamespace

#endif // PROJECT_H
