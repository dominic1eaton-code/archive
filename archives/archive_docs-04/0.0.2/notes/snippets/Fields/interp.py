import numpy as np;

def interp(a, xi, yi, x, y):
	## Linear interpolation - nice and quick because we are
	## working in grid-index coordinates.
	if type(xi) == np.ndarray:
		x = xi.astype(np.int)
		y = yi.astype(np.int)
	else:
		x = np.int(xi)
		y = np.int(yi)
	a00 = a[y,x]
	a01 = a[y,x+1]
	a10 = a[y+1,x]
	a11 = a[y+1,x+1]
	xt = xi - x
	yt = yi - y
	a0 = a00*(1-xt) + a01*xt
	a1 = a10*(1-xt) + a11*xt
	return a0*(1-yt) + a1*yt
		
		
if __name__ == '__main__':
	angle = 6 / 8
	theta = (np.pi * angle)

	x = np.linspace(-3,3,100)
	y = np.linspace(-3,3,100)
	u = np.ones(x.shape)* np.ones(y[:,np.newaxis].shape) * np.cos(theta)
	v = np.ones(x.shape)* np.ones(y[:,np.newaxis].shape) * np.sin(theta)
	speed = np.sqrt(u*u + v*v)	
	a = speed; 
	
	p = interp(a, 8, 20, x, y)
	
	# print(x)
	# print(y)
	# print(u)
	# print(v)
	print(p)