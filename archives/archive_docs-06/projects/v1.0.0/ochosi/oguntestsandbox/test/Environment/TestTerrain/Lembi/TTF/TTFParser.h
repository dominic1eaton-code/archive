/**
 * @brief
 * @note
 */
#include <stdint.h>
#include <vector>
#include <string>


namespace lembi
{

/**
 * array containing tags of tables and location offsets
 * in bytes
 */
 typedef struct
 {
    union
    {
        /**
         * 
         */
        char tagC[4];

        /**
         * 
         */
        uint32_t tag;
    };

    std::string ftag;

    /**
     * 
     */
    uint32_t checksum;

    /**
     * offset from start of file
     */
    uint32_t offset;

    /**
     * 
     */
    uint32_t length;
 } tableDirectory;

/**
 * Contains information about number of
 * tables in file and precalculations for
 * binary search of specific tables in file 
 */
typedef struct
{
    /**
     * type of font
     */
    uint32_t scalarType;

    /**
     * number of tables in file
     */
    uint16_t numTables;

    /**
     * specific tag binary search range
     */
    uint16_t searchRange;

    /**
     * specific tag binary search entry selection
     */
    uint16_t entrySelector;

    /**
     * specific tag binary search range shift
     */
    uint16_t rangeShift;
} offsetTable;


typedef struct 
{
    /**
     * 
     */
	uint16_t  format;

    /**
     * 
     */
 	uint16_t  length;

    /**
     * 
     */
 	uint16_t  language;

    /**
     * 
     */
 	uint16_t  segCountX2;

    /**
     * 
     */
 	uint16_t  searchRange;

    /**
     * 
     */
 	uint16_t  entrySelector;

    /**
     * 
     */
 	uint16_t  rangeShift;

    /**
     * 
     */
	uint16_t  reservedPad;

    /**
     * 
     */
	uint16_t  *endCode;

    /**
     * 
     */
	uint16_t  *startCode;

    /**
     * 
     */
	uint16_t  *idDelta;

    /**
     * 
     */
	uint16_t  *idRangeOffset;

    /**
     * 
     */
	uint16_t  *glyphIdArray;

    /**
     * 
     */
} format4;


typedef struct 
{
    /**
     * 
     */
	uint16_t platformID;

    /**
     * 
     */
	uint16_t platformSpecificID;

    /**
     * 
     */
	uint32_t offset;
} cmap_encoding_subtable;

typedef struct 
{
    /**
     * 
     */
	uint16_t version;

    /**
     * 
     */
	uint16_t numberSubtables;

    /**
     * 
     */
	cmap_encoding_subtable* subtables;
} cmap;


/**
 * Font Directory table
 */
typedef struct
{
    /**
     * table directories
     */
    std::vector<tableDirectory> tables;
    
    /**
     * offset tables
     */
    offsetTable offset;

    /**
     * 
     */
    format4* f4;

    /**
     * 
     */
	cmap* cmap;

    /**
     * 
     */
	char* glyf;

    /**
     * 
     */
	char* loca;

    /**
     * 
     */
	char* head;
} fontDirectory;

class TTFParser
{
public:
    TTFParser();

    virtual ~TTFParser(void);

    /**
     * Parse input .ttf file
     * @param filename name of file to parse
     */
    void parse(const std::string& filename);

private:
    uint32_t readbytes(uint32_t size);

    uint32_t readbytes(std::string data);

    /**
     * read all of the bytes from the specified file and return them in a byte 
     * array managed by std::vector. We start by opening the file with two flags:
     *      ate   : Start reading at the end of the file
     *      binary: Read the file as binary file (avoid text transformations)
     * @param filename name of file to read
     */
    std::vector<char> read(const std::string& filename);

    void parseOffsetTable();

    void parseTableDirectory();

    fontDirectory m_fontDirectory;

    std::vector<char> m_data;

    char* m_offset;

    uint32_t m_dataoffset;
    uint32_t u8 = sizeof(char);
    uint32_t u16 = sizeof(uint16_t);
    uint32_t u32 = sizeof(uint32_t);
    uint32_t u64 = sizeof(uint64_t);

    std::vector<std::string> fontTables = {
        "DSIG",
        "glyf",
        "loca",
        "head",
        "cmap"
    };
};


}; // namespace Lembi