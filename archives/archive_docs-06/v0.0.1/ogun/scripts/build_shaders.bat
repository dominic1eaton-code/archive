@echo off
REM
REM
REM

SET MOUNT=C:
SET GLSL_COMPILER=%MOUNT%/global/VulkanSDK/1.3.296.0/Bin/glslc.exe
SET SHADER_NAME=testshader0
SET SHADER_LIBRARY_PATH=%MOUNT%/dev/v0.0.1/ogun/assets/shaders
SET SHADER_SET=test
set SHADER_TYPES=vert frag
@REM set SHADER_TYPES=vert frag comp

for %%a in (%SHADER_TYPES%) do (
    %GLSL_COMPILER% %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a -o  %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a.spv
)