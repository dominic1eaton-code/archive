# feature/kernel_renderer todos engine v0.2.0
* lighting
    * [ ] bloom
    * [ ] shadow mapping
    * [ ] cube mapping
    * [ ] kernel lighting
    * [ ] area lights
    * [ ] light casters
    * [ ] HDR
    * [ ] PBR
    * [ ] IBR
* rendering
    * [ ] normal-tangent-bitangent axis per mesh / global axis rendering
    * [ ] endless grid
    * [ ] headless, offscreen rendering
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
        * fea, bim, ge, re, cad, cam vulkan app wrapper
        * game packaging and deployment vulkan app wrapper
* engine
    * [ ] architecture rewrite cleanup v0.2.0