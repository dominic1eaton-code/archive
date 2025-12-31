rem
rem 
rem

F:/VulkanSDK/1.3.204.0/Bin/glslc.exe shader.vert -o vert.spv
F:/VulkanSDK/1.3.204.0/Bin/glslc.exe shader.frag -o frag.spv

@REM F:/VulkanSDK/1.3.204.0/Bin/glslc.exe shader.geometry -o geometry.spv
@REM pause

cd D:\dev\projects\RenderEngine\assets\shaders\default
F:/VulkanSDK/1.3.204.0/Bin/glslc.exe lighting2.vert -o ../compiled/lighting2.vert.spv
F:/VulkanSDK/1.3.204.0/Bin/glslc.exe lighting2.frag -o ../compiled/lighting2.frag.spv


cmake -Bbuild -DCMAKE_INSTALL_PREFIX=%CD%/bin
cmake --install build

