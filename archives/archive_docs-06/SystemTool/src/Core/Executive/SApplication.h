/**
 * @brief Applications: Top level execution program to run
 *        Applications call Systems: Primary Computational unit
 *          apps can run as static state or dynamic services
 *        Systems call Processes: threads of executions
 *        Processes call components: Individual computation units to execute logic
 *        Components contain interfaces: Input output specification for data coming
 *                                       in/out of component computation logic unit
 *        Interfaces contain data: info state packets coming in/out from interface
 */

#include <string>
#include <vector>

class SComponentFactory;
class SCommunicationFactory;
class SBaseComponent;
class SSystemMode;
class SSystem;
class SystemList;
class SMode;

namespace SystemLTool
{
    class SApplication
    {
        public:
            SApplication();
            virtual ~SApplication(void);

            /* main application method */
            void call();

            /* Get application current running status */
            bool running() const {return m_isRunning;}

        private:
            /* Systems to be executed by application*/
            std::vector<SSystem*> m_systems;

            /* Application running status */
            bool m_isRunning;

            /** Application runtime ID */
            int id;
    };
} // SystemLTool