/**
 * @brief   
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifdef MATHLIB_EXPORT
#   define MATHLIB_API __declspec(dllexport)
#else
#   define MATHLIB_API __declspec(dllimport)
#endif

#define MATHLIB_ATTR
#define MATHLIB_CALL __cdecl
#define MATHLIB_PTR MATHLIB_CALL
