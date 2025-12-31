#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief
# @param ARCHITECTURE desired architecture to use
# @note
#-----------------------------------------------------------
macro(common_configure_architecture)
    if(${ARCHITECTURE} STREQUAL 64)
        set(BUILD_32_BIT FALSE)
        if(UNIX)
            string(REPLACE "-m32" "-m64" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
            string(REPLACE "-m32" "-m64" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")
        endif()
        set_property(GLOBAL PROPERTY BUILD_64_BIT TRUE)
        set(LIBSUFFIX "64")
        set(BITVER "64")
        if(MSCV)
            set(BINSUFFIX "64")
        else()
            set(BINSUFFIX "")
        endif()
        set(PROJECT_ARCHITECTURE "x64")
        elseif(${ARCHITECTURE} STREQUAL 32)
        set(BUILD_32_BIT TRUE)
        if(UNIX)
            string(REPLACE "-m32" "-m64" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
            string(REPLACE "-m32" "-m64" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")
        endif()
        set_property(GLOBAL PROPERTY BUILD_64_BIT FALSE)
        set(LIBSUFFIX "")
        set(BITVER "32")
        if(MSCV)
            set(BINSUFFIX "32")
        else()
            set(BINSUFFIX "")
        endif()
        set(PROJECT_ARCHITECTURE "x86")
        else()
        message(FATAL_ERROR "Unrecognized Architecture: ${ARCHITECTURE}")
    endif()
endmacro()