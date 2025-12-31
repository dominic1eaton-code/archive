/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VShaderManager_h
#define VShaderManager_h

#include <vector>
#include <fstream>

namespace ogun
{

/*
 * @brief: read all of the bytes from the specified file and return them in a byte 
 *         array managed by std::vector. We start by opening the file with two flags:
 *             ate   : Start reading at the end of the file
 *             binary: Read the file as binary file (avoid text transformations)
 */
std::vector<char> readFile(const std::string& filename)
{
    std::ifstream file(filename, std::ios::ate | std::ios::binary);
    if (!file.is_open())
    {
        throw std::runtime_error("failed to open file!");
    }

    // The advantage of starting to read at the end of the file is that we
    // can use the read position to determine the size of the file and allocate
    // a buffer
    size_t fileSize = (size_t) file.tellg();
    std::vector<char> buffer(fileSize);

    // seek back to the beginning of the file and read all of the bytes at once
    file.seekg(0);
    file.read(buffer.data(), fileSize);

    // close the file and return the bytes
    file.close();
    return buffer;
}

} // namespace ogun

#endif // VShaderManager_h