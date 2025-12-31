#pragma once

#include <vector>
#include <string>


#ifdef _WIN32
  #define ORU_EXPORT __declspec(dllexport)
#else
  #define ORU_EXPORT
#endif

ORU_EXPORT void oru();
ORU_EXPORT void oru_print_vector(const std::vector<std::string> &strings);
