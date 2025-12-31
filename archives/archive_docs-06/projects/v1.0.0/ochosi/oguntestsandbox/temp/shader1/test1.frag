precision mediump float;
uniform float uTime;   // This uniform is provided by the editor to the shaders every frame using the time provided by Three.js Clock
uniform float uRandom; // This uniform is provided by the editor to the shaders every frame using the javascript Math.random() function

void main()
{
    gl_FragColor = vec4(cos(uTime + (uRandom * 0.25)), cos(uTime), sin(uTime), 1.0);
}
