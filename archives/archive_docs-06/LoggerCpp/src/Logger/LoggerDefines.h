/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */
#pragma once

#ifdef LOGGER_EXPORT
#   define LOGGER_API __declspec(dllexport)
#else
#   define LOGGER_API __declspec(dllimport)
#endif

#define LOGGER_ATTR
#define LOGGER_CALL __cdecl
#define LOGGER_PTR LOGGER_CALL
