/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */
#pragma once

#ifndef LOGGER_H
#define LOGGER_H

#include "LoggerDefines.h"
#include <string>
#include <fstream>
#include <sstream>

// define logging constants
#define LOGGER_MAX_NAME_LENGTH 64
#define LOGGER_MAX_MESSAGE_LENGTH 4096

// Main package name space
namespace LoggingTool
{
    // default logging levels
    typedef enum
    {
        INFO = 0,
        DEBUG = 1,
        WARNING = 2,
        ERROR_ = 3,
        CRITICAL = 4,
    } LoggingLevel;
    static const char* LoggingLevelStrings[] = {"INFO", "DEBUG", "WARNING", "ERROR", "CRITICAL"};

    /*
     * Logging management
     * singleton Class
     */
    class LOGGER_API Logger
    {
    public:
        Logger();
        virtual ~Logger(void);

        // enable logging unit
        void enable();

        // disable logging unit
        void disable();

        // return enable status of logging unit  
        bool enabled() const;

        // main log perform function
        Logger& log(std::string  logUnit,
                    LoggingLevel loglevel);

        // specific log perform by type functions
        // template<class T> Logger& operator<<(const T& rhs); // @TODO: log generic template type
        Logger& operator<<(bool rhs);                       // log boolean type
        Logger& operator<<(short rhs);                      // log short int type
        Logger& operator<<(unsigned short rhs);             // log unsigned short int type
        Logger& operator<<(int rhs);                        // log log int type
        Logger& operator<<(unsigned int rhs);               // log log unsigned int type
        Logger& operator<<(long rhs);                       // log long int type
        Logger& operator<<(unsigned long rhs);              // log unsigned log int type
        Logger& operator<<(unsigned char rhs);              // log unsigned char type
        Logger& operator<<(const char* rhs);                // log const char type
        Logger& operator<<(float rhs);                      // log float type
        Logger& operator<<(double rhs);                     // log double type
        Logger& operator<<(const std::string& rhs);         // log string type
        
        // log char type. If endl terminating line character is passed 
        // to function, logger will terminate reading input and write
        // to designated output stream
        Logger& operator<<(char rhs);

        // terminating character end line which ends a logging output line
        inline static const char* const endl = NULL;

    private:
        // internal output logging
        void write();

        // convert numerically indexed enum value to string value
        const char* getTextForEnum(int enumVal) const;

        // is logging enabled ?
        bool m_isEnabled;

        // is verbose logging enabled ?
        bool m_isVerbose;

        // current logging unit
        std::string m_logunit;

        // current logging level
        LoggingLevel m_loglevel;

        // output log stream
        std::ostringstream m_ostream;

        // output log file
        std::ofstream m_logfile;
    };
} // LoggingTool

#endif // LOGGER_H
