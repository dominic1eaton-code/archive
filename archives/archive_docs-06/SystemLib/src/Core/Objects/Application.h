/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

#include <string>


class Application
{
public:
    Application();
    virtual ~Application(void);

    /* */
    void call();

    /* */
    const bool running();

private:
    /* */
    bool m_isRunning;

    /* */
    std::string id;


};
