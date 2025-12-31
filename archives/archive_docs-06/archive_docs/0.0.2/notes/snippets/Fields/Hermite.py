import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits import mplot3d
from math import sqrt

def HermCurve(t, P1, P2, T1, T2):
    # Hermite Curve coefficients
    a = 1 - 3*t**2 + 2*t**3
    b = t**2 *(3 - 2*t)
    c = t * (t - 1)**2
    d = t**2 * (t - 1)

    h = a*P1 + b*P2 + c*T1 + d*T2

    # return hermite curve point at parametric value t
    return h

if __name__ == '__main__':
    # t = np.array([0, 0.5, 1])
    #
    # P1 = np.array([0, 0])
    # P2 = np.array([1, 1])
    #
    # T1 = np.array([0, 0])
    # T2 = np.array([0, 0])
    #
    # x = np.linspace(0, 1, 10)
    #
    # # x = np.linspace(0, np.linalg.norm(P2), 10)
    #
    #
    # # 2D
    # for i in range(len(x)-1):
    #     H = HermCurve(x[i], P1, P2, T1, T2)
    #     plt.scatter(H[0], H[1])
    #
    # # plt.plot(x_new, cubic_interp1d(x_new, x, y))
    #
    # plt.show()


    # 3D
    P1 = np.array([0, 0, 0])
    P2 = np.array([10, 10, 10])

    T1 = np.array([0, -2, 1])
    T2 = np.array([0, 0, 0])

    x = np.linspace(0, 1, 10)

    fig = plt.figure()
    ax = plt.axes(projection='3d')
    for i in range(len(x)-1):
        H = HermCurve(x[i], P1, P2, T1, T2)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');

    plt.show()
