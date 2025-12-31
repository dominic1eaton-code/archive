@echo off
REM @copyright
REM @brief
SET MOUNT=C:
SET GLSL_COMPILER=%MOUNT%/global/Vulkan/1.3.296.0/Bin/glslc.exe
SET SHADER_LIBRARY_PATH=%MOUNT%/dev/projects/ogun-render-engine/assets/shaders
@REM SET SHADER_LIBRARY_PATH=%MOUNT%/dev/projects/emchoro/ossain/oru/ogun/assets/shaders

SET SHADER_SET=headless
SET SHADER_NAME=default_headless
@REM SET SHADER_SET=lighting
@REM SET SHADER_NAME=default_lighting
@REM SET SHADER_SET=terrain
@REM SET SHADER_NAME=default_terrain
@REM SET SHADER_SET=particle
@REM SET SHADER_NAME=default_particle
set SHADER_TYPES=comp
@REM set SHADER_TYPES=vert frag
@REM set SHADER_TYPES=vert frag comp
@REM set SHADER_TYPES=vert frag tesc tese
for %%a in (%SHADER_TYPES%) do (
    echo %GLSL_COMPILER% %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a -o  %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a.spv
    %GLSL_COMPILER% %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a -o  %SHADER_LIBRARY_PATH%/%SHADER_SET%/%SHADER_NAME%.%%a.spv
)