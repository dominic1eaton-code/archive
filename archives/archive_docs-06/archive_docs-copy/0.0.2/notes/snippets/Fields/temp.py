-25200.0
""" This is a very old version of streamplot. Matplotlib has included
streamplot from version 1.2. The matplotlib version has many
improvements over the version in this file, and is better integrated
and more stable than this code.

See
http://tonysyu.github.com/plotting-streamlines-with-matplotlib-and-sympy.html
"""

def stream(x, y, u, v, density=1, linewidth=1,
               color='k', cmap=None, norm=None, vmax=None, vmin=None,
               arrowsize=1, INTEGRATOR='RK4'):
	## Set up some constants - size of the grid used.
	gridsizeX = len(x)
	gridsizeY = len(y)

	## Constants used to convert between grid index coords and user coords.
	DX = x[1]-x[0]
	DY = y[1]-y[0]
	XOFF = x[0]
	YOFF = y[0]

	## Now rescale velocity onto axes-coordinates
	u = u / (x[-1]-x[0])
	v = v / (y[-1]-y[0])
	speed = numpy.sqrt(u*u+v*v)

	## s (path length) will now be in axes-coordinates, but we must
	## rescale u for integrations.
	u *= NGX
	v *= NGY


	## Blank array: This is the heart of the algorithm. It begins life
	## zeroed, but is set to one when a streamline passes through each
	## box. Then streamlines are only allowed to pass through zeroed
	## boxes. The lower resolution of this grid determines the
	## approximate spacing between trajectories.
	if type(density) == float or type(density) == int:
	assert density > 0
		NBX = int(30*density)
		NBY = int(30*density)
	else:
		assert len(density) > 0
		NBX = int(30*density[0])
		NBY = int(30*density[1])
	blank = numpy.zeros((NBY,NBX))

	## Constants for conversion between grid-index space and
	## blank-index space
	bx_spacing = NGX/float(NBX-1)
	by_spacing = NGY/float(NBY-1)

	
	def blank_pos(xi, yi):
	## Takes grid space coords and returns nearest space in
	## the blank array.
	return int((xi / bx_spacing) + 0.5), \
		   int((yi / by_spacing) + 0.5)	
	
	def value_at(a, xi, yi):
		## Linear interpolation - nice and quick because we are
		## working in grid-index coordinates.
		if type(xi) == numpy.ndarray:
			x = xi.astype(numpy.int)
			y = yi.astype(numpy.int)
		else:
			x = numpy.int(xi)
			y = numpy.int(yi)
		a00 = a[y,x]
		a01 = a[y,x+1]
		a10 = a[y+1,x]
		a11 = a[y+1,x+1]
		xt = xi - x
		yt = yi - y
		a0 = a00*(1-xt) + a01*xt
		a1 = a10*(1-xt) + a11*xt
		return a0*(1-yt) + a1*yt
		
	def rk4_integrate(x0, y0):
		## This function does RK4 forward and back trajectories from
		## the initial conditions, with the odd 'blank array'
		## termination conditions. TODO tidy the integration loops.

		# forward
		def f(xi, yi):
			dt_ds = 1./value_at(speed, xi, yi)
			ui = value_at(u, xi, yi)
			vi = value_at(v, xi, yi)
			return ui*dt_ds, vi*dt_ds

		# backward
		def g(xi, yi):
			dt_ds = 1./value_at(speed, xi, yi)
			ui = value_at(u, xi, yi)
			vi = value_at(v, xi, yi)
			return -ui*dt_ds, -vi*dt_ds

		check = lambda xi, yi: xi>=0 and xi<NGX-1 and yi>=0 and yi<NGY-1

		bx_changes = []
		by_changes = []
		
        ## Integrator function
        def rk4(x0, y0, f):
            ds = 0.01 #min(1./NGX, 1./NGY, 0.01)
            stotal = 0
            xi = x0
            yi = y0
            xb, yb = blank_pos(xi, yi)
            xf_traj = []
            yf_traj = []
            while check(xi, yi):
                # Time step. First save the point.
                xf_traj.append(xi)
                yf_traj.append(yi)
                # Next, advance one using RK4
                try:
                    k1x, k1y = f(xi, yi)
                    k2x, k2y = f(xi + .5*ds*k1x, yi + .5*ds*k1y)
                    k3x, k3y = f(xi + .5*ds*k2x, yi + .5*ds*k2y)
                    k4x, k4y = f(xi + ds*k3x, yi + ds*k3y)
                except IndexError:
                    # Out of the domain on one of the intermediate steps
                    break
                xi += ds*(k1x+2*k2x+2*k3x+k4x) / 6.
                yi += ds*(k1y+2*k2y+2*k3y+k4y) / 6.
                # Final position might be out of the domain
                if not check(xi, yi): break
                stotal += ds
                # Next, if s gets to thres, check blank.
                new_xb, new_yb = blank_pos(xi, yi)
                if new_xb != xb or new_yb != yb:
                    # New square, so check and colour. Quit if required.
                    if blank[new_yb,new_xb] == 0:
                        blank[new_yb,new_xb] = 1
                        bx_changes.append(new_xb)
                        by_changes.append(new_yb)
                        xb = new_xb
                        yb = new_yb
                    else:
                        break
                if stotal > 2:
                    break
            return stotal, xf_traj, yf_traj
		
		
		## Forward and backward trajectories
        if INTEGRATOR == 'RK4':
            integrator = rk4
		
		sf, xf_traj, yf_traj = integrator(x0, y0, f) # foward
        sb, xb_traj, yb_traj = integrator(x0, y0, g) # backward
        stotal = sf + sb
        x_traj = xb_traj[::-1] + xf_traj[1:]
        y_traj = yb_traj[::-1] + yf_traj[1:]
		
        ## Tests to check length of traj. Remember, s in units of axes.
        if len(x_traj) < 1: return None
        if stotal > .2:
            initxb, inityb = blank_pos(x0, y0)
            blank[inityb, initxb] = 1
            return x_traj, y_traj
        else:
            for xb, yb in zip(bx_changes, by_changes):
                blank[yb, xb] = 0
            return None

			
		
		
		
		
		
		
		
		