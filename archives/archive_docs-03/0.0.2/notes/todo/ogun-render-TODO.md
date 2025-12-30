# feature/kernel_renderer todos engine release v0.2.0 - v1.0.0
* lighting
    * [ ] bloom
    * [ ] shadow mapping
    * [ ] cube mapping
    * [ ] kernel lighting
    * [ ] area lights
    * [x] light casters
    * [ ] HDR
    * [ ] PBR
    * [ ] IBR
* rendering
    * [ ] object picking, movement
    * [ ] ray (cube) marching
    * [ ] ray tracing
    * [ ] normal-tangent-bitangent axis per mesh / global axis rendering
    * [ ] endless grid
    * [ ] headless, offscreen rendering, screenshot
    * [ ] deferred rendering
    * [ ] dynamic rendering
    * [ ] text rendering
    * [ ] basic ui rendering
    * [ ] instance rendering
    * [ ] skybox cubemap
    * [ ] primitives rendering
        * line, hermite spline, bezier spline, point, sphere, circle, hexagon, n-polygon, cone, pyramid, prism, square, rectangle
* animation
    * [ ] basic skeleton model
    * [ ] basic skeleton animation modelling
* scene
    * [ ] basic scene graph
    * [ ] frustrum culling
    * [ ] scene object creation system
* shaders
    * [x] compute shader for basic particle system generation
    * [ ] compute shader for basic n body system generation
    * [ ] geometry shader for normal visuatlization
    * [ ] tesselation shader for terrain generation
    * [ ] shader hot reloading and editing
* models
    * [ ] model loading
    * [ ] modelling texture, normal, shadow mapping
    * [ ] terrain height map
    * [ ] move model in render scene via keyboard, mouse, gamepad
* linux
    * [ ] run app in linux xwindow
    * [ ] setup platform configuration for windows, linux
* CI/CD
    * [ ] support linux, windows sandbox builds
    * [ ] setup gitlab runner pipeline
    * [ ] setup package manager, environment configuration
    * [ ] setup sandbox commands
        * configure, build, install, test, package, tag, (checksum) deploy
* system
    * [ ] setup threadpool, multithreaded execution model
    * [ ] setup publish subscribe model
    * [ ] setup server-client, reactor model
    * [ ] setup application fsm
* application
    * [ ] vulkan application wrapper
        * vulkan api wrapper library
        * game packaging and deployment vulkan app wrapper
        * fea, bim, ge, re, cad, cam vulkan app wrapper - oru platform
            * vulkan api wrapper library - ogun
                * render engine - moremi
                * game engine - oru
                * FEA engine - elegua
                * CAD engine - yewa
                * CAM engine - dada
                    * slicer
                    * gcode
                * BIM engine - iroko
                * DES engine - aroni
                * editor engine - eshu
                * 3D modelling engine - imole
                * simulation engine - yota
* physics
    * [ ] rigid body
    * [ ] particle physics
* engine
    * [ ] architecture rewrite cleanup v0.2.0
    * [ ] unit tests
    * [ ] documentation
    * [ ] simd and optimizations
* simulation
    * [ ] base editor
        * [ ] basic 3d model editor
        * [ ] basic scene/level editor
        * [ ] basic game editor
        * [ ] basic shader editor
        * [ ] basic fluid editor
        * [ ] basic animation editor
        * [ ] basic terrain editor
        * [ ] basic environment editor
    * [ ] water fluid sim
    * [ ] cloud sim
    * [ ] smoke sim
    * [ ] fire sim
    * [ ] vortex sim
    * [ ] beam sim
    * [ ] hex war game
    * [ ] fula village game
    * [ ] basic drive sim
    * [ ] basic flight sim
