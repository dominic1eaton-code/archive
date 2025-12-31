rem 
rem
rem

SET MOUNT=C:
@REM %MOUNT%/VulkanSDK/x.x.x.x/Bin32/glslc.exe shader.vert -o vert.spv
@REM %MOUNT%/VulkanSDK/x.x.x.x/Bin32/glslc.exe shader.frag -o frag.spv

%MOUNT%/global/VulkanSDK/1.3.296.0/Bin/glslc.exe test0.vert -o test0.vert.spv
%MOUNT%/global/VulkanSDK/1.3.296.0/Bin/glslc.exe test0.frag -o test0.frag.spv

pause
