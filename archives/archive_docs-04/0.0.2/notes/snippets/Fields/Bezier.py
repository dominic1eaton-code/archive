import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits import mplot3d
from math import sqrt

from Triangulate import Triangulate, drawTriangle

def BezierCurve(t, P1, P2, T1, T2):
    # Hermite Curve coefficients
    a = (1 - t)**3
    b = 3*t*(1 - t)**2
    c = 3 * t**2 * (1 - t)
    d = t**3

    h = a*P1 + b*P2 + c*T1 + d*T2

    # return hermite curve point at parametric value t
    return h

def CubicInterp(t, P1, P2, T1, T2):
    # Hermite Curve coefficients
    a = 2*t**3 - 3*t**2 + 1
    b = t**3 - 2*t**2 + t
    c = t**3 - t**2
    d = -2*t**3 + 3*t**2

    h = a*P1 + b*T1 + c*T2 + d*P2

    # return hermite curve point at parametric value t
    return h


def drawPrism(points):
    z = 0

def Test():
    # 3D
    P1 = np.array([-0, 0, 100])
    P2 = np.array([-0, 100, 0])

    # T1 = np.array([0, 0, 0])
    # T2 = np.array([-0, 0, 0])
    T1 = np.array([0, 0, 0])
    T2 = np.array([0, -10, 10])

    x = np.linspace(0, 1, 10)

    Vertices = []

    fig = plt.figure()
    ax = plt.axes(projection='3d')
    for i in range(len(x) - 1):
        H = CubicInterp(x[i], P1, P2, T1, T2)
        Vertices.append(H)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');

    width = 500
    # P1 = P1 + np.array([0, -width, 0])
    # P2 = P2 + np.array([-width / 5, width, 0])
    P1 = P1 + np.array([width, 0, 0])
    P2 = P2 + np.array([width, 0, 0])

    # T1 = np.array([1500, 0, 0])
    # T2 = np.array([-1500, 0, 0])

    # T1 = np.array([-450, -80, 0])
    # T2 = np.array([450, -80, 0])

    # x = np.linspace(0, 1, 2)

    # fig = plt.figure()
    # ax = plt.axes(projection='3d')

    Htemp = []
    for i in range(len(x) - 1):
        H = CubicInterp(x[i], P1, P2, T1, T2)
        Htemp.append(H)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');

    for i in reversed(range(len(Htemp))):
        Vertices.append(Htemp[i])

    plt.show()

    # plot triangles
    Vertices.reverse()  # Counter Clockwise
    triangles = Triangulate(Vertices)

    fig = plt.figure()
    ax = plt.axes(projection='3d')
    for i in range(len(triangles)):
        drawTriangle(triangles[i], ax)

    plt.show()

def Prism(l=0, w=0, h=0, points=[]):
    # Prism points
    Points = []

    origin = np.array([0, 0, 0])
    length = -10
    width = -5
    height = -2

    # Counter clockwise points
    p0 = origin
    p1 = origin + np.array([0, -length, 0])
    p2 = origin + np.array([-width, -length, 0])
    p3 = origin + np.array([-width, 0, 0])
    p4 = origin + np.array([0, 0, -height])
    p5 = origin + np.array([0, -length, -height])
    p6 = origin + np.array([-width, -length, -height])
    p7 = origin + np.array([-width, 0, -height])

    Points.append(p0)
    Points.append(p1)
    Points.append(p2)
    Points.append(p3)
    Points.append(p4)
    Points.append(p5)
    Points.append(p6)
    Points.append(p7)

    Top = []
    Bottom = []
    Front = []
    Back = []
    Left = []
    Right = []

    Faces = []

    Top.append(p0)
    Top.append(p1)
    Top.append(p2)
    Top.append(p3)

    Bottom.append(p4)
    Bottom.append(p5)
    Bottom.append(p6)
    Bottom.append(p7)

    Front.append(p0)
    Front.append(p3)
    Front.append(p7)
    Front.append(p4)

    Back.append(p1)
    Back.append(p5)
    Back.append(p6)
    Back.append(p2)

    Left.append(p0)
    Left.append(p1)
    Left.append(p5)
    Left.append(p4)

    Right.append(p3)
    Right.append(p2)
    Right.append(p6)
    Right.append(p7)

    Faces.append(Top)
    Faces.append(Bottom)
    Faces.append(Front)
    Faces.append(Back)
    Faces.append(Left)
    Faces.append(Right)

    fig = plt.figure()
    ax = plt.axes(projection='3d')
    for i in range(len(Points)):
        ax.scatter([Points[i][0], Points[(i + 1) % 3][0]], \
                   [Points[i][1], Points[(i + 1) % 3][1]], \
                   [Points[i][2], Points[(i + 1) % 3][2]])
    plt.show()

    fig = plt.figure()
    ax = plt.axes(projection='3d')
    for i in range(len(Faces)):
        triangles = Triangulate(Faces[i])

        for i in range(len(triangles)):
            drawTriangle(triangles[i], ax)

    plt.show()

def DrawFace(face, t, ax, T1, T2):
    Vertices = []

    for i in range(len(t)):
        H = CubicInterp(t[i], face[0], face[1], T1, T2)
        Vertices.append(H)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');

    Htemp = []
    for i in range(len(t)):
        # H = CubicInterp(t[i], p0 + np.array([width, 0, 0]), p1 + np.array([width, 0, 0]), T1, T2)
        H = CubicInterp(t[i], face[3], face[2], T1, T2)
        Htemp.append(H)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');

    for i in reversed(range(len(Htemp))):
        Vertices.append(Htemp[i])

    # plot triangles
    Vertices.reverse()  # Counter Clockwise
    triangles = Triangulate(Vertices)

    # Faces.append(Vertices)
    Vertices = []

    for i in range(len(triangles)):
        drawTriangle(triangles[i], ax)



if __name__ == '__main__':
    # Test()

    # Draw Prism
    # by dimension or by points
    # Prism()

    Vertices = []
    Faces = []

    origin = np.array([0, 0, 0])
    length = 200
    width  = 20
    height = 1

    # parametric parameter
    t = np.linspace(0, 1, 8)

    # Counter clockwise points
    p0 = origin
    p1 = origin + np.array([0, length, 0])
    p2 = origin + np.array([width, length, 0])
    p3 = origin + np.array([width, 0, 0])
    p4 = origin + np.array([0, 0, height])
    p5 = origin + np.array([0, length, height])
    p6 = origin + np.array([width, length, height])
    p7 = origin + np.array([width, 0, height])

    Top = []
    Bottom = []
    Front = []
    Back = []
    Left = []
    Right = []

    Faces = []

    Top.append(p0)
    Top.append(p1)
    Top.append(p2)
    Top.append(p3)

    Bottom.append(p4)
    Bottom.append(p5)
    Bottom.append(p6)
    Bottom.append(p7)

    Left.append(p0)
    Left.append(p1)
    Left.append(p5)
    Left.append(p4)

    Right.append(p3)
    Right.append(p2)
    Right.append(p6)
    Right.append(p7)


    Front.append(p0)
    Front.append(p4)
    Front.append(p7)
    Front.append(p3)

    Back.append(p1)
    Back.append(p5)
    Back.append(p6)
    Back.append(p2)

    Faces.append(Top)
    Faces.append(Bottom)
    Faces.append(Left)
    Faces.append(Right)
    Faces.append(Front)
    Faces.append(Back)

    T1 = np.array([-10, 0, -10])
    T2 = np.array([0, -0, -10])

    fig = plt.figure()
    ax = plt.axes(projection='3d')

    for i in range(len(Faces)-2):
        DrawFace(Faces[i],t, ax, T1, T2)

    # T1 = np.array([0, -100, 0])
    # T2 = np.array([0, 150, -50])
    #
    # for i in range((len(Faces))-2, len(Faces)):
    #     DrawFace(Faces[i],t, ax, T1, T2)

    # Draw Center spline interpolation points
    T1 = np.array([-10, 0, -10])
    T2 = np.array([0, -0, -10])

    start_pt = np.array([width / 2, 0, 0])
    end_pt = np.array([width / 2, length, 0])

    for i in range(len(t)):
        H = CubicInterp(t[i], start_pt, end_pt, T1, T2)
        Vertices.append(H)
        ax.scatter3D(H[0], H[1], H[2], cmap='Greens');


    plt.show()


