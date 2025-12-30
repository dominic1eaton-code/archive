""" This is a very old version of streamplot. Matplotlib has included
streamplot from version 1.2. The matplotlib version has many
improvements over the version in this file, and is better integrated
and more stable than this code.

See
http://tonysyu.github.com/plotting-streamlines-with-matplotlib-and-sympy.html
"""

version = '4'

import pylab
import matplotlib
import matplotlib.patches as mpp
import numpy as np
import matplotlib.pyplot as plt

def streamplot(x, y, u, v, center=np.array([0, 0]),  density=1, linewidth=1,
               color='k', cmap=None, norm=None, vmax=None, vmin=None,
               arrowsize=1, INTEGRATOR='RK4'):
    '''Draws streamlines of a vector flow.

    * x and y are 1d arrays defining an *evenly spaced* grid.
    * u and v are 2d arrays (shape [y,x]) giving velocities.
    * density controls the closeness of the streamlines. For different
      densities in each direction, use a tuple or list [densityx, densityy].
    * linewidth is either a number (uniform lines) or a 2d array
      (variable linewidth).
    * color is either a color code (of any kind) or a 2d array. This is
      then transformed into color by the cmap, norm, vmin and vmax args.
      A value of None gives the default for each.

    INTEGRATOR is experimental. Currently, RK4 should be used.
      '''

    ## Sanity checks.
    # check input vector dimensions
    assert len(x.shape)==1
    assert len(y.shape)==1
    assert u.shape == (len(y), len(x))
    assert v.shape == (len(y), len(x))
    if type(linewidth) == np.ndarray:
        assert linewidth.shape == (len(y), len(x))
    if type(color) == np.ndarray:
        assert color.shape == (len(y), len(x))

    ## Set up some constants - size of the grid used.
    NGX = len(x)
    NGY = len(y)
    ## Constants used to convert between grid index coords and user coords.
    DX = x[1]-x[0]
    DY = y[1]-y[0]
    XOFF = x[0]
    YOFF = y[0]

    ## Now rescale velocity onto axes-coordinates
    u = u / (x[-1]-x[0])
    v = v / (y[-1]-y[0])
    speed = np.sqrt(u*u+v*v)
    ## s (path length) will now be in axes-coordinates, but we must
    ## rescale u for integrations.
    u *= NGX
    v *= NGY
    ## Now u and v in grid-coordinates.

    ## Blank array: This is the heart of the algorithm. It begins life
    ## zeroed, but is set to one when a streamline passes through each
    ## box. Then streamlines are only allowed to pass through zeroed
    ## boxes. The lower resolution of this grid determines the
    ## approximate spacing between trajectories.
    if type(density) == float or type(density) == int:
        assert density > 0
        NBX = int(2*density)
        NBY = int(2*density)
    else:
        assert len(density) > 0
        NBX = int(2*density[0])
        NBY = int(2*density[1])
    blank = np.zeros((NBY,NBX))

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

    def rk4_integrate(x0, y0):
        ## This function does RK4 forward and back trajectories from
        ## the initial conditions, with the odd 'blank array'
        ## termination conditions. TODO tidy the integration loops.

        def f(xi, yi):
            dt_ds = 1./value_at(speed, xi, yi)
            ui = value_at(u, xi, yi)
            vi = value_at(v, xi, yi)
            return ui*dt_ds, vi*dt_ds

        def g(xi, yi):
            dt_ds = 1./value_at(speed, xi, yi)
            ui = value_at(u, xi, yi)
            vi = value_at(v, xi, yi)
            return -ui*dt_ds, -vi*dt_ds

        check = lambda xi, yi: xi>=0 and xi<NGX-1 and yi>=0 and yi<NGY-1

        bx_changes = []
        by_changes = []

        ## Integrator function
        def rk4(x0, y0, f, c):
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

        ## Alternative Integrator function

        ## RK45 does not really help in it's current state. The
        ## resulting trajectories are accurate but low-resolution in
        ## regions of high curvature and thus fairly ugly. Maybe a
        ## curvature based cap on the maximum ds permitted is the way
        ## forward.


        ## Forward and backward trajectories
        integrator = rk4

        sf, xf_traj, yf_traj = integrator(x0, y0, f, center)
        sb, xb_traj, yb_traj = integrator(x0, y0, g, center)
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

    ## A quick function for integrating trajectories if blank==0.
    trajectories = []
    def traj(xb, yb):
        if xb < 0 or xb >= NBX or yb < 0 or yb >= NBY:
            return
        if blank[yb, xb] == 0:
            t = rk4_integrate(xb*bx_spacing, yb*by_spacing)
            if t != None:
                trajectories.append(t)

    ## Now we build up the trajectory set. I've found it best to look
    ## for blank==0 along the edges first, and work inwards.
    for indent in range(int((max(NBX,NBY))/2)):
        for xi in range(int(max(NBX,NBY)-2*indent)):
            traj(xi+indent, indent)
            traj(xi+indent, NBY-1-indent)
            traj(indent, xi+indent)
            traj(NBX-1-indent, xi+indent)

    return trajectories

def grid():
    angle = 4/4
    theta = (np.pi * angle)

    w = 200
    x = np.linspace(-w,w,w)
    y = np.linspace(-w,w,w)
    u = np.ones(x.shape)* np.ones(y[:,np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape)* np.ones(y[:,np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0])
        yt = np.array(t[1])
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0])
        yt = np.array(t[1])
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    plt.show()

def radial():
    angle = 3/4
    theta = (np.pi * angle)

    w = 100

    center = np.array([100, 100])


    # x = np.linspace(-w,w,w)
    # y = np.linspace(-w,w,w)

    # u =( y ** 2  - x ** 2 )+ np.zeros(y[:, np.newaxis].shape)
    # v = -2*x*y + np.zeros(y[:, np.newaxis].shape)
    y, x = np.mgrid[-w:w:100j, -w:w:100j]
    # field sectioning
    # y = y - center[1]
    # x = x - center[0]
    u = (y**2 )
    v = -2*x*y

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    x = np.linspace(-w,w,w)
    y = np.linspace(-w,w,w)
    trajectories = streamplot(x, y, u, v, center=center, density=4, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    # u2 = -2*x*y + np.zeros(y[:, np.newaxis].shape)
    # v2= -((y ** 2 - x ** 2) + np.zeros(y[:, np.newaxis].shape))
    y, x = np.mgrid[-w:w:100j, -w:w:100j]
    # field sectioning
    # y = y - center[1]
    # x = x - center[0]
    u2 = -2 * x * y
    v2 = -(y**2)
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    trajectories2 = streamplot(x, y, u2, v2, center=center, density=4, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1])- center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    plt.show()

def mixfield():
    #########################################################################################3
    # Grid 1
    angle = 4 / 4
    theta = (np.pi * angle)
    center = np.array([0, 0])

    w = 200
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    u = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0])- center[0]
        yt = np.array(t[1])- center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    #########################################################################################3
    # Grid 2
    angle = 3 / 4
    theta = (np.pi * angle)
    center = np.array([0, 200])

    w = 200
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    u = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    #########################################################################################3
    # Grid 3
    angle = 2 / 4
    theta = (np.pi * angle)
    center = np.array([200, 200])

    w = 200
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    u = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    #########################################################################################3
    # Grid 4
    angle = 2 / 4
    theta = (np.pi * angle)
    center = np.array([400, 200])

    w = 200
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    u = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    #########################################################################################3
    # Grid 5
    angle = 2 / 4
    theta = (np.pi * angle)
    center = np.array([400, 400])

    w = 200
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    u = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.cos(theta)
    v = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    trajectories = streamplot(x, y, u, v, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    u2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * np.sin(theta)
    v2 = np.ones(x.shape) * np.ones(y[:, np.newaxis].shape) * - np.cos(theta)
    trajectories2 = streamplot(x, y, u2, v2, density=2, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    #########################################################################################3
    # Radial 1
    w = 200
    center = np.array([200, 0])

    y, x = np.mgrid[-w:w:200j, -w:w:200j]
    # field sectioning
    # y = y - center[1]
    # x = x - center[0]
    u = (y ** 2)
    v = -2 * x * y

    fig = plt.figure(1)
    fig.suptitle("Streamlines", fontsize=16)
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    trajectories = streamplot(x, y, u, v,  density=4, INTEGRATOR='RK4', color='b')

    for t in trajectories:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    # u2 = -2*x*y + np.zeros(y[:, np.newaxis].shape)
    # v2= -((y ** 2 - x ** 2) + np.zeros(y[:, np.newaxis].shape))
    y, x = np.mgrid[-w:w:200j, -w:w:200j]
    # field sectioning
    # y = y - center[1]
    # x = x - center[0]
    u2 = -2 * x * y
    v2 = -(y ** 2)
    x = np.linspace(-w, w, w)
    y = np.linspace(-w, w, w)
    trajectories2 = streamplot(x, y, u2, v2,  density=4, INTEGRATOR='RK4', color='b')

    for t in trajectories2:
        xt = np.array(t[0]) - center[0]
        yt = np.array(t[1]) - center[1]
        for i in range(len(xt)):
            plt.scatter(xt[i], yt[i])

    plt.show()
if __name__ == '__main__':
    # mixfield()
    radial()
