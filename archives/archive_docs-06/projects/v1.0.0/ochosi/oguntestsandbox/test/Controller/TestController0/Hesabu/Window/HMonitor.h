/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

 #pragma once
 #ifndef HMonitor_h
 #define HMonitor_h
 
 #include <vector>
 
 namespace ogun
 {
 
 template<class U>
 class HMonitor
 {
 public:
     HMonitor();
     virtual ~HMonitor(void) = default;
 
 private:
 
    /**
     * @brief monitor ID
     */
    uint32_t id;

 };
 
 } // namespace ogun
 
 #endif // HMonitor_h