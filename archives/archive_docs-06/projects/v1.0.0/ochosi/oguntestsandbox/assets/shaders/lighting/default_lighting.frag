// @header
// @copyright
// @brief
// @note 
#version 450

//
layout(location = 0) in vec4 iColor;
layout(location = 1) in vec2 iTexture;
layout(location = 2) in vec3 iNormal;
layout(location = 3) in vec3 iPosition;

//
layout(location = 0) out vec4 oColor;

//
layout(binding = 2) uniform sampler2D texsampler;

layout(binding = 3) uniform GPUView
{
    vec4 position;
} view;

struct DirLight
{
    vec4 direction;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
};

struct PointLight 
{
    vec4 position;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
    float k0;
    float k1;
    float k2;
};

layout(binding = 4) uniform sampler2D texdiffuse[];

layout(binding = 5) uniform GPUCursor
{
    vec4 position;
} cursor;

// layout(binding = 6) uniform OPixel
// {
//     vec4 ocolor;
// } opixel;

// layout(std140, binding = 1) buffer GPUMesh
// {
//     GPUMeshData models[];
// } meshes;

vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir);
vec4 CalcPointLight(PointLight light, vec3 normal, vec3 fragPos, vec3 viewDir, float shine);

void main()
{
    vec3 norm = normalize(iNormal);
    vec3 viewDir = normalize(vec3(view.position.x, view.position.y, view.position.z) - iPosition);
    vec4 result = vec4(0.0, 0.0, 0.0, 1.0);
    float shine = .1;

    // compute lighting
    // DirLight light0;
    // light0.ambient = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.diffuse = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.specular = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.direction = vec4(-10.5f, -10.0f, 10.0f, 1.0);
    // result += CalcDirLight(light0, shine, norm, viewDir);
    // vec4 result = CalcDirLight(dirLight.light[iInstance], norm, viewDir);
    
    PointLight plight0;
    plight0.position = vec4(0.0, 0.0, 0.0, 1.0f);
    plight0.ambient = vec4(80.0f, 180.0f, 180.0f, 1.0f);
    plight0.diffuse = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    plight0.specular = vec4(0.5f, 0.5f, 0.5f, 1.0f);
    plight0.k0 = 0.1f;

    // // if (view.position.x-8 < gl_FragCoord.x && view.position.y-31 < gl_FragCoord.y)
    // if ((view.position.x-8 < gl_FragCoord.x && view.position.x+31 > gl_FragCoord.x) &&
    //     (view.position.y-31 < gl_FragCoord.y && view.position.y+31 > gl_FragCoord.y))
    // {
    //     plight0.k1 = 10.0f;
    // }
    // else
    // {
        plight0.k1 = 30.0f;
    // }
    // if (view.position.y-30 < gl_FragCoord.y)
    // {
    //     plight0.k2 = 2.0f;
    // }
    // else
    // {
        plight0.k2 = 20.0f;
    // }

    // plight0.k1 = iPosition.x;//float(view.position.x) / 10; //20.0; //cursor.position.x;// / 10;
    plight0.k2 = .2;
    result += CalcPointLight(plight0, norm, iPosition, viewDir, shine);

    // PointLight p1;
    // p1.position = vec4(-0.5f, 0.5f, 1.0f, 1.0f);
    // p1.ambient = vec4(10.0f, 110.0f, 190.0f, 1.0f);
    // p1.diffuse = vec4(1.0f, 1.0f, 1.0f, 1.0f);
    // p1.specular = vec4(1.0f, 1.0f, 1.0f, 1.0f);
    // p1.k0 = 0.1f;
    // p1.k1 = .02f;
    // p1.k2 = .07f;
    // result += CalcPointLight(p1, norm, iPosition, viewDir, shine);

    // PointLight p2;
    // p2.position = vec4(5.0, 5.0, 5.0, 1.0f);
    // p2.ambient = vec4(50.0f, 190.0f, 10.0f, 1.0f);
    // p2.diffuse = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    // p2.specular = vec4(0.5f, 0.5f, 0.5f, 1.0f);
    // p2.k0 = 0.1f;
    // p2.k1 = 1.0f;
    // p2.k2 = .022f;
    // result += CalcPointLight(p2, norm, iPosition, viewDir, shine);

    //////////////////////////////////////////////////////////////////////////////
    // vec3 outlineColor = {1.0, 1.0, 0.0};
    // vec2 textureSize = {20.0, 20.0};
    // float outlineThickness = 1.0f;
    // vec2 offx = vec2(outlineThickness / textureSize.x, 0.0);
    // vec2 offy = vec2(0.0, outlineThickness / textureSize.y);
    // float surroundingAlphaSum = texture(texsampler, iTexture.xy + offx).a +
    //                             texture(texsampler, iTexture.xy - offx).a +
    //                             texture(texsampler, iTexture.xy + offy).a +
    //                             texture(texsampler, iTexture.xy - offy).a;
    // // This pixel
    // vec4 pixel = texture(texsampler, iTexture.xy);
    // // If one of the surrounding pixels is transparent --> an edge is detected
    // if (4.0 * pixel.a - surroundingAlphaSum > 0.0)
    //     pixel = vec4(outlineColor, 1.0);
    // else
    //     pixel = vec4(0.5); // semi transparent
    // oColor = texture(texsampler, vec2(iTexture.x+.16, iTexture.y-0.06));
    //////////////////////////////////////////////////////////////////////////////

    float depth = gl_FragCoord.z;
    float near = 0.1;
    float far  = 100.0;
    float ndc = depth * 2.0 - 1.0;
    float linearDepth = (2.0 * near * far) / (far + near - ndc * (far - near));
    float dd = linearDepth / far;
    vec3 d = vec3(dd*2, 0.0, 0.0);

    /* fragment selection */
    vec2 cpos_color;
    cpos_color.x = ((view.position.x + 1) / 2);
    cpos_color.y = (view.position.y + 1) / 2;
    vec2 gfrag;
    gfrag.x =  (gl_FragCoord.x / 600);
    if (gl_PrimitiveID == 0 || gl_PrimitiveID == 1 ||
        gl_PrimitiveID == 2 || gl_PrimitiveID == 3 ||
        gl_PrimitiveID == 4 || gl_PrimitiveID == 5 ||
        gl_PrimitiveID == 6 || gl_PrimitiveID == 7 ||
        gl_PrimitiveID == 8 || gl_PrimitiveID == 9 ||
        gl_PrimitiveID == 10 || gl_PrimitiveID == 11)
    {
        // -(2*(cposx / (windowRect.left - windowRect.right)) + 1)
        // gfrag.y = 864 - 600;
        // if(cpos_color.x-.1 < gfrag.x && gfrag.x < cpos_color.x+.1)
        // if (gfrag.x < cpos_color.x)
        // {
            // oColor = vec4(gfrag.x, 0, 0, 1.0);
        oColor = vec4(1, 0, 0, 1.0);
        // }
        // else
        // {
        //     oColor = vec4(0, 0, 0, 1.0);
        // }
        // oColor = vec4(cpos_color.x , cpos_color.y, 0, 1.0);// * texture(texsampler, iTexture);
    }
    else
    {
        oColor = result * texture(texsampler, iTexture);
    }
    // opixel.color = vec4(1.0, 1.0, gl_PrimitiveID, 1.0f);
    // oColor = vec4(d, 1.0);// * texture(texsampler, iTexture);
    // oColor = result * iColor * texture(texsampler, iTexture);
    // oColor = iColor;
}

// calculates the color when using a directional light.
vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir)
{
    // vec3 lightDir = normalize(-vec3(light.direction.x, light.direction.y, light.direction.z));
    vec3 lightDir = normalize(-light.direction.xyz);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDir, reflectDir), 0.0), shine);
    // combine results
    vec4 ambient = light.ambient * texture(texsampler, iTexture);
    vec4 diffuse = light.diffuse * diff * texture(texsampler, iTexture);
    vec4 specular = light.specular * spec * texture(texsampler, iTexture);
    return (ambient + diffuse + specular);
}

vec4 CalcPointLight(PointLight light, vec3 normal, vec3 fragPos, vec3 viewDir, float shine)
{
    vec3 lightDir = normalize(light.position.xyz - fragPos);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDir, reflectDir), 0.0), shine);
    // attenuation
    float distance = length(light.position.xyz - fragPos);
    float attenuation = 1.0 / (light.k0 + light.k1 * distance + light.k2 * (distance * distance));    
    // combine results
    vec4 ambient = light.ambient * texture(texsampler, iTexture);
    vec4 diffuse = light.diffuse * diff * texture(texsampler, iTexture);
    vec4 specular = light.specular * spec * texture(texsampler, iTexture);
    ambient *= attenuation;
    diffuse *= attenuation;
    specular *= attenuation;
    return (ambient + diffuse + specular);
}


// #version 450

// // Created by inigo quilez - iq/2013
// // License Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License.

// // Some geometric orbit traps in the Mandelbrot set. More info:
// //
// // https://iquilezles.org/www/articles/ftrapsgeometric/ftrapsgeometric.htm

// // antialiasing level (squared)
// #define AA 3

// layout (location = 0) in vec3 inColor;

// layout (location = 0) out vec4 outFragColor;

// void mainImage( out vec4 fragColor, in vec2 fragCoord)
// {
//     vec2 iResolution = vec2(1700.f,900.f);
//     float iTime = 0;
//     vec3 col = vec3(0.0);

//     for( int m=0; m<AA; m++ )
//     for( int n=0; n<AA; n++ )
//     {
        
//     vec2 p = (2.0*(fragCoord+vec2(float(m),float(n))/float(AA))-iResolution.xy) / iResolution.y;

//     float zoo = 1.0/(400.0 - 150.0*sin(0.15*iTime-0.3));

//     vec2 cc = vec2(-0.533516,0.526141) + p*zoo;

//     vec2 t2c = vec2(-0.5,2.0);
//     t2c += 0.5*vec2( cos(0.13*(iTime-10.0)), sin(0.13*(iTime-10.0)) );
        
//     // iterate
//     vec2 z  = vec2(0.0);
//     vec2 dz = vec2(0.0);
//     float trap1 = 0.0;
//     float trap2 = 1e20;
//     float co2 = 0.0;
//     for( int i=0; i<150; i++ )
//     {
//         if( dot(z,z)>1024.0 ) break;

//         // Z' -> 2·Z·Z' + 1
//         dz = 2.0*vec2(z.x*dz.x-z.y*dz.y, z.x*dz.y + z.y*dz.x ) + vec2(1.0,0.0);
            
//         // Z -> Z² + c			
//         z = cc + vec2( z.x*z.x - z.y*z.y, 2.0*z.x*z.y );
            
//         // trap 1
//         float d1 = abs(dot(z-vec2(0.0,1.0),vec2(0.707)));
//         float ff = step( d1, 1.0 );
//         co2 += ff;
//         trap1 += ff*d1;

//         //trap2
//         trap2 = min( trap2, dot(z-t2c,z-t2c) );
//     }

//     // distance, d(c) = |Z|·log|Z|/|Z'|
//     float d = sqrt( dot(z,z)/dot(dz,dz) )*log(dot(z,z));

//     float c1 = pow( clamp( 2.00*d/zoo,    0.0, 1.0 ), 0.5 );
//     float c2 = pow( clamp( 1.5*trap1/co2, 0.0, 1.0 ), 2.0 );
//     float c3 = pow( clamp( 0.4*trap2, 0.0, 1.0 ), 0.25 );

//     vec3 col1 = 0.5 + 0.5*sin( 3.0 + 4.0*c2 + vec3(0.0,0.5,1.0) );
//     vec3 col2 = 0.5 + 0.5*sin( 4.1 + 2.0*c3 + vec3(1.0,0.5,0.0) );
//     col += 2.0*sqrt(c1*col1*col2);
//     }
//     col /= float(AA*AA);

//     fragColor = vec4( col, 1.0 );
// }

// void main() 
// {
// 	mainImage(outFragColor, gl_FragCoord.xy);
// }

