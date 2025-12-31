cmake_minimum_required(VERSION 3.15)
project(oru CXX)




add_library(oru src/oru.cpp)
target_include_directories(oru PUBLIC include)



set_target_properties(oru PROPERTIES PUBLIC_HEADER "include/oru.h")
install(TARGETS oru)
