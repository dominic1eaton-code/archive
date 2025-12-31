/**
 * @copyright
 * @brief
 * @note
 */

#ifndef ogun_app_h
#define ogun_app_h

#include <string>

namespace ogun
{

inline const std::string default_config_file = "engine.ini";

void run_app();
void read_config();

}; // namespace ogun

#endif // ogun_app_h