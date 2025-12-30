import numpy as np
import matplotlib.pyplot as plt
from Streamlines import Streamlines


def radial(p):
    a = (p[1] ** 2 - p[0] ** 2)
    b = -2 * p[0] * p[1]
    return np.array([a, b])

def radial2(p):
    a = -2 * p[0] * p[1]
    b = -(p[1] ** 2 - p[0] ** 2)
    return np.array([a, b])

def grid(p, r, theta):
    a = r * np.cos(2*theta)
    b = r * np.sin(2*theta)
    return np.array([a, b])


def grid2(p, r, theta):
    a = r * np.sin(2*theta)
    b = - r * np.cos(2*theta)
    return np.array([a, b])


def rk2(tspan, y0, dt):
    t0 = tspan[0]
    tN = tspan[1]
    N = int(np.floor((tN - t0) / dt) + 1)

    tout = np.linspace(t0, tN, num=N)
    h = tout[1] - tout[0]

    yout = np.zeros([N, np.size(y0, 0)])
    yout[0, :] = y0
    y = y0

    for i in range(1, N):
        k = radial(y)
        y = y + h*radial2(y + (h/2)*k)
        yout[i, :] = y

    return yout, tout

def rk4(tspan, y0, dt, angle, center=np.array([0, 0]), dimen='major', type='grid'):
    t0 = tspan[0]
    tN = tspan[1]
    N = int(np.floor((tN - t0) / dt) + 1)

    tout = np.linspace(t0, tN, num=N)
    h = tout[1] - tout[0]

    yout = np.zeros([N, np.size(y0, 0)])
    yout[0, :] = y0
    y = y0

    if type == 'grid':
        for i in range(1, N):
            if dimen == 'major':
                k1 = grid2((y-center), 1, angle)
                k2 = grid2((y-center) + (h/2) * k1, 1,  angle)
                k3 = grid2((y-center) + (h/2) * k2, 1, angle)
                k4 = grid2((y-center) + h * k3, 1, angle)
            else:
                k1 = grid((y-center), 1, angle)
                k2 = grid((y-center) + (h / 2) * k1, 1, angle)
                k3 = grid((y-center) + (h / 2) * k2, 1, angle)
                k4 = grid((y-center) + h * k3, 1, angle)
            y = y + (h/6)*(k1 + 2*k2 + 2*k3 + k4)
            yout[i, :] = y
    elif type == 'radial':
        for i in range(1, N):
            if dimen == 'major':
                k1 = radial2((y-center))
                k2 = radial2((y-center) + (h/2) * k1)
                k3 = radial2((y-center) + (h/2) * k2)
                k4 = radial2((y-center) + h * k3)
            else:
                k1 = radial((y-center))
                k2 = radial((y-center) + (h / 2) * k1)
                k3 = radial((y-center) + (h / 2) * k2)
                k4 = radial((y-center) + h * k3)
            y = y + (h/6)*(k1 + 2*k2 + 2*k3 + k4)
            yout[i, :] = y

    return yout, tout

if __name__ == "__main__":
    x0 = np.array([2, 2])
    dt = .1
    tspan = [-100, 100]
    center = np.array([0 , 0])
    angle = 2 / 8
    theta = (np.pi * angle)
    # x, t = rk2(tspan, x0, dt)
    # plt.scatter(x[:, 0], x[:, 1])
    # for i in range(10, 20, 2):
    #     for j in range(10, 20, 2):
    #         x0 = np.array([i, -j])
    #         x, t = rk2(tspan, x0, dt)
    #         plt.scatter(x[:, 0], x[:, 1])
    ###########################################################################################
    fig = plt.figure()
    fig.suptitle("Streamlines", fontsize=16)

    ax = plt.subplot("211")
    ax.set_title("Major")
    for i in range(100, 200, 10):
        x0 = np.array([i, 200])
        x, t = rk4(tspan, x0, dt, angle,  center, 'major', 'grid')
        plt.scatter(x[:, 0], x[:, 1])

    ax = plt.subplot("212")
    ax.set_title("Minor")
    for i in range(100, 200, 10):
        x0 = np.array([i, 0])
        x, t = rk4(tspan, x0, dt, angle, np.array([0, 0]), 'minor', 'grid')
        plt.scatter(x[:, 0], x[:, 1])

    plt.show()

    ###########################################################################################
    # for i in range(100, 200, 10):
    #     x0 = np.array([i, 200])
    #     x, t = rk4(tspan, x0, dt, angle,  center, 'major', 'grid')
    #     plt.scatter(x[:, 0], x[:, 1])
    #
    # for i in range(100, 400, 40):
    #     x0 = np.array([i, 200])
    #     x, t = rk4(tspan, x0, dt, angle, np.array([0, 0]), 'minor', 'grid')
    #     plt.scatter(x[:, 0], x[:, 1])
    #
    # plt.show()
