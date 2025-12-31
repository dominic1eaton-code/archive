/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#pragma once
#ifndef VULKANCONSTANTS_h
#define VULKANCONSTANTS_h

namespace RenderEngine::Constants
{
    // We choose the number 2 because we don't want the CPU to get too far ahead of the GPU.
    // With 2 frames in flight, the CPU and the GPU can be working on their own tasks at the
    // same time. If the CPU finishes early, it will wait till the GPU finishes rendering before
    // submitting more work. With 3 or more frames in flight, the CPU could get ahead of the GPU
    // adding frames of latency. Generally, extra latency isn't desired. But giving the application
    // control over the number of frames in flight is another example of Vulkan being explicit.
    const int MAX_FRAMES_IN_FLIGHT = 3; // using 3 for smoother frame updates

    // Maximum number of renderable objects in a render batch
    const int MAX_OBJECTS = 10000;
} // VulkanEngine::Constants

#endif // VULKANCONSTANTS_h
