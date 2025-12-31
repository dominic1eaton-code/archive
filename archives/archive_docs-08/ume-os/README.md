# umeOS
organization operating system

- create organization applications (firms, business, non profits, enterprises, etsc...)
- organization applications are used by organization operators (founders, employees, managers, directors, clients, stakeholders, etc...)
- OS manages organization infrastrustructure, "hardware" and "devices, such as physical devices (e.g. servers, mobile devices, electronic point of sales systems, etc...)
  - OS manages "device drivers" represented as 3rd party business applications management (e.g. quickbooks, jira, gitlab, asana, strategic management system platform, etc...)
    - OS provides high level centralized interface to connect organization "device drivers", automated workflows accross device driver platforms,  (e.g. quickbooks to manage finances and budgets that updates strategic managment and accounting systems, which further automatically updates project management system budgets, which updates strategic management system platforms in an automated workflow/process)
- organization OS+kernel provides single, centralized, distributable, deployable, configurable interface that sits between organization "devices (3rd party business apps, custom business apps)" and organization applications and operators


           HIGH LEVEL ORGANIZATION-OS DIAGRAM

                +--------------+
                | organization | (stakeholders, founders, owners, clients, shareholders, investors, employees, managers, directors)
                | operator     |
                +--------------+
                        |
                        |
                +--------------+
                | organization |
                | application  |------> value (proposition), solutions, products, services, applications, systems, assets, capabilities, outcomes
                |    (firm)    |
                +--------------+
                        |
                        |
         +-------------------------------+
         |          organization         |
         |            operating          | (business model [generator,manager,adminsitration])
         |             system            | (strategies, plans, operations, automations, processes, data, storage/memory)
         +-------------------------------+
         |  organization kernel, modules |
         |      (logical infrastructure) |
         |                               |
         | * strategic management module |
         | * administration module       |
         | * HR module                   |
         | * IT module                   |
         | * misc., custom,              |
         |      template module, etc...  |
         +-------------------------------+
                        |
                        |
                +-------------------+
                | organization      |
                | (physical/system) |
                | infrastructure    |---------------------------------------------------+-----------------------------+------------------------+
                +-------------------+                                                   |                             |                        |
                      |  |                                                   +---------------------+                  |                        |
                      |  +----------------------------+------------- -+      |     organization    |       +-----------------------+           |
            +---------+---------+                     |               |      |       "device"      |       |     organization      |           |
            |         |         |           +-------------------+     |      | strategic management|       |       "device"        |           |
    +--------------+  |  +-------------+    |   organization    |     |      |  system integration |       | operations management |           |
    | organization |  |  |organization |    |    "device"       |     |      +---------------------+       |  system integration   |           |
    |   "device"   |  |  |  "device"   |    | e.g. gitlab       |     |                                    +-----------------------+           |
    |  e.g. server |  |  | e.g. POS    |    | integration system|     |                                                                        |
    +--------------+  |  |      system |    +-------------------+     +--------------+-----------------------+                     +-----------------------+ 
                      |  +-------------+                              |              |                       |                     |     organization      |
                +--------------+                             +-----------------+     |                       |                     |       "device"        |
                | organization |                             |  organization   |     |                       |                     |     HR management     |
                | "device"     |                             |    "device"     |     |                       |                     |  system integration   |
                |  e.g. mobile |                             | e.g. quickbooks |     |                       |                     +-----------------------+
                |       devuce |                             |     integration |     |              +-----------------+
                +--------------+                             +-----------------+     |              |   organization  |
                                                                                     |              |     "device"    |
                                                                            +-----------------+     | e.g. mangomint  |
                                                                            |   organization  |     |     integration |
                                                                            |     "device"    |     +-----------------+
                                                                            | e.g. click up   |
                                                                            |    integration  |
                                                                            +-----------------+
