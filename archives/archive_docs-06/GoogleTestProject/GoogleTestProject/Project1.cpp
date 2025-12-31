/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */

#include "Project1.h"

using namespace ProjectNamespace;

Project1::Project1()
	: m_value(0)
	, m_enabled(false)
{}

Project1::~Project1() {}


/* PUBLIC FUNCTIONS */
void Project1::incValue(int offset)
{
	m_value += offset;
}

int Project1::getValue()
{
	return m_value;
}

void Project1::enable()
{
	m_enabled = true;
}

void Project1::disable()
{
	m_enabled = false;
}

bool Project1::enabled()
{
	return m_enabled;
}
