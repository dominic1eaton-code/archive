"""
    @see https://stackoverflow.com/questions/42147776/producing-2d-perlin-noise-with-numpy
"""
#%matplotlib inline
import numpy as np
import matplotlib.pyplot as plt

def perlin(x,y,seed=0):
    # permutation table
    np.random.seed(seed)
    p = np.arange(256,dtype=int)
    np.random.shuffle(p)
    p = np.stack([p,p]).flatten()
    # coordinates of the first corner
    xi = x.astype(int)
    yi = y.astype(int)
    # internal coordinates
    xf = x - xi
    yf = y - yi
    # fade factors
    u = fade(xf)
    v = fade(yf)
    # noise components
    n00 = gradient(p[p[xi]+yi],xf,yf)
    n01 = gradient(p[p[xi]+yi+1],xf,yf-1)
    n11 = gradient(p[p[xi+1]+yi+1],xf-1,yf-1)
    n10 = gradient(p[p[xi+1]+yi],xf-1,yf)
    # combine noises
    x1 = lerp(n00,n10,u)
    x2 = lerp(n10,n11,u)
    return lerp(x2,x1,v)

def lerp(a,b,x):
    "linear interpolation"
    return a + x * (b-a)

def fade(t):
    "6t^5 - 15t^4 + 10t^3"
    return 6 * t**5 - 15 * t**4 + 10 * t**3

def gradient(h,x,y):
    "grad converts h to the right gradient vector and return the dot product with (x,y)"
    vectors = np.array([[0,1],[0,-1],[1,0],[-1,0]])
    g = vectors[h%4]
    return g[:,:,0] * x + g[:,:,1] * y

lin = np.linspace(0,5,100,endpoint=False)
y,x = np.meshgrid(lin,lin)

# c = plt.imshow(z, cmap ='Greens', vmin = z_min, vmax = z_max, 
#                  extent =[x.min(), x.max(), y.min(), y.max()], 
#                     interpolation ='nearest', origin ='lower') 

c = plt.imshow(perlin(x,y,seed=0))
plt.colorbar(c)
plt.title('Perlin Noise',fontweight ="bold") 
plt.show() 