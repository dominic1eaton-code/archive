/**
 * @license
 * @brief vulkan renderer test fixtures
 */
#include "vulkan_renderer_fixture.h"
#include "vulkan_model.h"

ogun::test::VulkanRendererFixture::VulkanRendererFixture()
{
    ogun::init_model();
}

ogun::test::VulkanRendererFixture::~VulkanRendererFixture()
{
    ogun::shutdown_model();
}

// vim: set ts=4 sw=4 sts=4 expandtab:
// EOF