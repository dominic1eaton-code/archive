from mpl_toolkits.mplot3d import Axes3D
import matplotlib.pyplot as plt
import numpy as np

# Fixing random state for reproducibility
np.random.seed(19680801)


def randrange(n, vmin, vmax):
    '''
    Helper function to make an array of random numbers having shape (n, )
    with each number distributed Uniform(vmin, vmax).
    '''
    return (vmax - vmin)*np.random.rand(n) + vmin

def gen_points(w):
	x = np.linspace(0, w, w)
	y = np.linspace(0, w, w)
	z =  np.ones(w)
	p = np.array([x, y, z])
	return p
	
	
fig = plt.figure()
ax = fig.add_subplot(111, projection='3d')

n = 10

"""
# For each set of style and range settings, plot n random points in the box
# defined by x in [23, 32], y in [0, 100], z in [zlow, zhigh].
for c, m, zlow, zhigh in [('r', 'o', -50, -25), ('b', '^', -30, -5)]:
    xs = randrange(n, 23, 32)
    ys = randrange(n, 0, 100)
    zs = randrange(n, zlow, zhigh)
    ax.scatter(xs, ys, zs, c=c, marker=m)
"""

"""
w = 10
lin = np.linspace(0, w, w)
xs = randrange(n, 0, 40)
ys = randrange(n, 0, 40)
zs = randrange(n, 0, 1)

o =  np.ones(w)


for i in range(w):
	ax.scatter(lin, o+i, o, c='r')
"""
	
p = gen_points(n)
x, 
y = np.meshgrid(p[0, :], p[1, :])
P = []

for i in range(n):
	for j in range(n):
		ax.scatter(p[0, i], p[1, j], 1, c='r')
		P.append([p[0, i], p[1, j], 1])

print(P)
ax.set_xlabel('X Label')
ax.set_ylabel('Y Label')
ax.set_zlabel('Z Label')

plt.show()