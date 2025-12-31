/**
 * @brief
 * @note
 */


#include "lembi_ttf_parser.h"
#include <cstring>
#include <iostream>
#include <fstream>
#include <string>
#include <bitset>
#include <filesystem>


using namespace lembi;

TTFParser::TTFParser()
    : m_dataoffset(0)
{}

TTFParser::~TTFParser(void)
{}


std::vector<char> TTFParser::read(const std::string& filename)
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


void TTFParser::parse(const std::string& filename)
{
    // read data file
    m_data = read(filename);

    int a = 1;
    auto v = (decltype(a))2.1;
    
    // read offset table
    m_fontDirectory.offset.scalarType = readbytes(u32);
    m_fontDirectory.offset.numTables = readbytes(u16);
    m_fontDirectory.offset.searchRange = readbytes(u16);
    m_fontDirectory.offset.entrySelector = readbytes(u16);
    m_fontDirectory.offset.rangeShift = readbytes(u16);

    // read font tables
    uint32_t length = 0;
    m_fontDirectory.tables.resize(m_fontDirectory.offset.numTables);
    for (int t = 0; t < m_fontDirectory.tables.size(); t++)
    {
        m_fontDirectory.tables[t].tag = readbytes(u32);
        m_fontDirectory.tables[t].checksum = readbytes(u32);
        m_fontDirectory.tables[t].offset = readbytes(u32);
        m_fontDirectory.tables[t].length = readbytes(u32);
    
        length +=  m_fontDirectory.tables[t].length;
    
        for (int c = 3; c >= 0; c--)
        {
            m_fontDirectory.tables[t].ftag += m_fontDirectory.tables[t].tagC[c];
        }
    }


}

uint32_t TTFParser::readbytes(uint32_t size)
{
    uint32_t data = 0;
    for (int i = m_dataoffset%size; i <= (m_dataoffset+(size-1))%size; i++)
    {
        data |= (uint8_t)m_data[m_dataoffset + i] << (((m_dataoffset+(size-1))%size)-i)*8;
    }
    m_dataoffset += size;
    return data;
}

uint32_t TTFParser::readbytes(std::string data)
{
    uint32_t datav = 0;
    uint32_t size = data.size();
    for (int i = 0; i < size; i++)
    {
        datav |= (uint8_t)data[i] << (size-i)*8;
    }
    return datav;
}


 int main()
 {
    std::filesystem::path mount = "C:";
    std::string fontPath = "/dev/projects/ogun/0.2.0/source/assets/fonts";
    std::string fontType = "arial";
    std::string fontName = "ARIAL";
    std::string fontExt = ".ttf";
    std::filesystem::path arialFont = mount / fontPath /  fontType / (fontName + fontExt);
    std::string arial = arialFont.string();

	uint32_t filesize = 0;
    lembi::TTFParser* parser = new lembi::TTFParser();
    // std::vector<char> arialFile = parser->read(arial.c_str());
    parser->parse(arial.c_str());

    return 0;
 }

