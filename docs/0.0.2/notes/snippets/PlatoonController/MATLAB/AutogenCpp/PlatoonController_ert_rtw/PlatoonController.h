//
// Academic License - for use in teaching, academic research, and meeting
// course requirements at degree granting institutions only.  Not for
// government, commercial, or other organizational use.
//
// File: PlatoonController.h
//
// Code generated for Simulink model 'PlatoonController'.
//
// Model version                  : 1.1
// Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
// C/C++ source code generated on : Tue Dec  4 16:20:25 2018
//
// Target selection: ert.tlc
// Embedded hardware selection: Intel->x86-64 (Windows64)
// Code generation objectives:
//    1. Execution efficiency
//    2. RAM efficiency
// Validation result: Not run
//
#ifndef RTW_HEADER_PlatoonController_h_
#define RTW_HEADER_PlatoonController_h_
#ifndef PlatoonController_COMMON_INCLUDES_
# define PlatoonController_COMMON_INCLUDES_
#include "rtwtypes.h"
#include "rtw_continuous.h"
#include "rtw_solver.h"
#endif                                 // PlatoonController_COMMON_INCLUDES_

// Macros for accessing real-time model data structure
#ifndef rtmGetErrorStatus
# define rtmGetErrorStatus(rtm)        ((rtm)->errorStatus)
#endif

#ifndef rtmSetErrorStatus
# define rtmSetErrorStatus(rtm, val)   ((rtm)->errorStatus = (val))
#endif

#ifndef rtmGetT
# define rtmGetT(rtm)                  (rtmGetTPtr((rtm))[0])
#endif

#ifndef rtmGetTPtr
# define rtmGetTPtr(rtm)               ((rtm)->Timing.t)
#endif

// Forward declaration for rtModel
typedef struct tag_RTM RT_MODEL;

// Real-time Model Data Structure
struct tag_RTM {
  const char_T * volatile errorStatus;
  RTWSolverInfo solverInfo;

  //
  //  Timing:
  //  The following substructure contains information regarding
  //  the timing information for the model.

  struct {
    uint32_T clockTick0;
    time_T stepSize0;
    SimTimeStep simTimeStep;
    time_T *t;
    time_T tArray[1];
  } Timing;
};

// Class declaration for model PlatoonController
class PlatoonControllerModelClass {
  // public data and function members
 public:
  // model initialize function
  void initialize();

  // model step function
  void step();

  // Constructor
  PlatoonControllerModelClass();

  // Destructor
  ~PlatoonControllerModelClass();

  // Real-Time Model get method
  RT_MODEL * getRTM();

  // private data and function members
 private:
  // Real-Time Model
  RT_MODEL rtM;
};

//-
//  These blocks were eliminated from the model due to optimizations:
//
//  Block '<S6>/Aggregate' : Unused code path elimination
//  Block '<S9>/Gain' : Unused code path elimination
//  Block '<S10>/Gain' : Unused code path elimination
//  Block '<S11>/Gain' : Unused code path elimination
//  Block '<S12>/Gain' : Unused code path elimination
//  Block '<S13>/Gain' : Unused code path elimination
//  Block '<S14>/Sum of Elements' : Unused code path elimination
//  Block '<S16>/Aggregator' : Unused code path elimination
//  Block '<S17>/Aggregator' : Unused code path elimination
//  Block '<S21>/Aggregate' : Unused code path elimination
//  Block '<S23>/Gain' : Unused code path elimination
//  Block '<S24>/Gain' : Unused code path elimination
//  Block '<S25>/Gain' : Unused code path elimination
//  Block '<S26>/Gain' : Unused code path elimination
//  Block '<S27>/Gain' : Unused code path elimination
//  Block '<S22>/Aggregator' : Unused code path elimination
//  Block '<S18>/Aggregator' : Unused code path elimination
//  Block '<S8>/Aggregate' : Unused code path elimination
//  Block '<S32>/Gain' : Unused code path elimination
//  Block '<S33>/Gain' : Unused code path elimination
//  Block '<S34>/Gain' : Unused code path elimination
//  Block '<S35>/Gain' : Unused code path elimination
//  Block '<S36>/Gain' : Unused code path elimination
//  Block '<Root>/Reference' : Unused code path elimination
//  Block '<Root>/Sum' : Unused code path elimination


//-
//  The generated code includes comments that allow you to trace directly
//  back to the appropriate location in the model.  The basic format
//  is <system>/block_name, where system is the system number (uniquely
//  assigned by Simulink) and block_name is the name of the block.
//
//  Use the MATLAB hilite_system command to trace the generated code back
//  to the model.  For example,
//
//  hilite_system('<S3>')    - opens system 3
//  hilite_system('<S3>/Kp') - opens and selects block Kp which resides in S3
//
//  Here is the system hierarchy for this model
//
//  '<Root>' : 'PlatoonController'
//  '<S1>'   : 'PlatoonController/Platoon Controller'
//  '<S2>'   : 'PlatoonController/Vehicle System'
//  '<S3>'   : 'PlatoonController/Platoon Controller/HLC'
//  '<S4>'   : 'PlatoonController/Platoon Controller/LLC'
//  '<S5>'   : 'PlatoonController/Platoon Controller/PLC'
//  '<S6>'   : 'PlatoonController/Platoon Controller/PLC/Estimator'
//  '<S7>'   : 'PlatoonController/Platoon Controller/PLC/Optimizer'
//  '<S8>'   : 'PlatoonController/Platoon Controller/PLC/Predictor'
//  '<S9>'   : 'PlatoonController/Platoon Controller/PLC/Estimator/Fca'
//  '<S10>'  : 'PlatoonController/Platoon Controller/PLC/Estimator/Fcrowd'
//  '<S11>'  : 'PlatoonController/Platoon Controller/PLC/Estimator/Fgroup'
//  '<S12>'  : 'PlatoonController/Platoon Controller/PLC/Estimator/Fhomogeneity'
//  '<S13>'  : 'PlatoonController/Platoon Controller/PLC/Estimator/Foa'
//  '<S14>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/Decider'
//  '<S15>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer'
//  '<S16>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Safety'
//  '<S17>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability'
//  '<S18>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Vehicle'
//  '<S19>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Safety/Adversary'
//  '<S20>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Safety/Danger'
//  '<S21>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock'
//  '<S22>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Stabilize'
//  '<S23>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock/Fca'
//  '<S24>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock/Fcrowd'
//  '<S25>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock/Fgroup'
//  '<S26>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock/Fhomogeneity'
//  '<S27>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Flock/Foa'
//  '<S28>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Stabilize/Regulation'
//  '<S29>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Stability/Stabilize/Stability'
//  '<S30>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Vehicle/Interests'
//  '<S31>'  : 'PlatoonController/Platoon Controller/PLC/Optimizer/SubOptimizer/Vehicle/Survival'
//  '<S32>'  : 'PlatoonController/Platoon Controller/PLC/Predictor/Fca'
//  '<S33>'  : 'PlatoonController/Platoon Controller/PLC/Predictor/Fcrowd'
//  '<S34>'  : 'PlatoonController/Platoon Controller/PLC/Predictor/Fgroup'
//  '<S35>'  : 'PlatoonController/Platoon Controller/PLC/Predictor/Fhomogeneity'
//  '<S36>'  : 'PlatoonController/Platoon Controller/PLC/Predictor/Foa'

#endif                                 // RTW_HEADER_PlatoonController_h_

//
// File trailer for generated code.
//
// [EOF]
//
