/**
 * @copyright DEFAULT
 * @brief: Draw Triangle render test
 * @note : N/A
 */

#include <iostream>
#include "GPUObject.h"


struct GPUCameraData
{
    glm::mat4 view;
    glm::mat4 projection;
    glm::mat4 viewprojection;
};


class GPUCamera : public GPUObject
{
public:
    GPUCamera();

    virtual ~GPUCamera(void);

    /* Bind logical camera data to memory that will be used on the GPU */
    void bind();

private:
    /* */
    GPUCameraData m_cameraData;
};
