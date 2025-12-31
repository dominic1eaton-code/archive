/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */

#include "Logger.h"
#include <iostream>

int main()
{
    std::cout << "test logging function 0" << std::endl;
    LoggingTool::Logger* logger = new LoggingTool::Logger();
    std::cout << "test logging function 1" << std::endl;
    logger->enable();
    std::cout << "test logging function 2 " << logger->enabled() << std::endl;
    logger->log("main", LoggingTool::LoggingLevel::INFO) << "TESTING LOGGING" << LoggingTool::Logger::endl;
    std::cout << "test logging function 3" << std::endl;
    return 0;
}
