import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits import mplot3d
from math import sqrt

epsilon = 0.001

def normalize(v):
    norm = np.linalg.norm(v)
    if norm == 0:
       return v
    return v / norm

def computeNormal(p0, p1, p2):
    u = p1 - p0
    v = p2 - p0
    return np.cross(u, v)

def getNextActive(x, vertexCount, active):
    while True:
        x = x + 1
        if x == vertexCount:
            x = 0
        if active[x]:
            return x

def getPrevActive(x, vertexCount, active):
    while True:
        x = x - 1
        if x == 1:
            x = vertexCount - 1
        if active[x]:
            return x


# def Triangulate_EC(vertices):
#     vertexCount = len(vertices)
#     triangleIndices = []
#     active = []
#
#     triangleCount = 0
#     start = 0
#
#     earFound = False
#
#     if vertexCount < 3:
#         return np.array([0, 0, 0])
#     if vertexCount == 3:
#         return vertices
#     p1 = 0
#     p2 = 1
#     m1 = vertexCount - 1
#     m2 = vertexCount - 2
#
#
#     for i in range(len(vertices)):
#         active.append(True)
#


def Hull(P):
    a = 0

    return a

def Merge(H1, H2):
    a = 0

    return a

def SortByX(P):
    sPoints = []
    # for i in range(len(P)):


    return sPoints

# Convex Hull Divide and Conquer
def ConvexHull_DC(vertices):
    A = []  # Lower coordinates
    B = []  # Upper coordinates

    P = SortByX(vertices)

    HA = Hull(A)
    HB = Hull(B)

    M = Merge(HA, HB)

def Triangulate(vertices):
    vertexCount = len(vertices)
    triangleIndices = []
    active = []

    triangleCount = 0
    start = 0

    p1 = 0                  # p0
    p2 = 1                  # p1
    m1 = vertexCount - 1    # m0
    m2 = vertexCount - 2    # m1

    lastPositive = False

    if vertexCount < 3:
        return np.array([0, 0, 0])

    # mark all vertices as active for checking
    for i in range(len(vertices)):
        active.append(True)

    # for i in range(len(vertices)):
    while True:
        # Check if only three vertices remain
        if (p2 == m2):
            t = np.array([m1, p1, p2])
            triangleIndices.append(t)
            break

        # Determine if vp1, vp2, and vm1 form valid triangle
        vp1 = vertices[p1]
        vp2 = vertices[p2]
        vm1 = vertices[m1]
        vm2 = vertices[m2]
        positive = False
        negative = False

        normal = np.cross(vm1 - vp1, vm1 - vp2)

        # Positve sided triangle
        n1 = np.cross(normal, normalize(vm1 - vp2))

        if (np.dot(n1, vp1 - vp2) > epsilon):
            positive = True
            n2 = np.cross(normal, normalize(vp1 - vm1))
            n3 = np.cross(normal, normalize(vp2 - vp1))

            for a in  range(vertexCount - 1):
                # Look for more vertices inside triangle
                if (active[a] and (a != p1 and (a != p2 and (a != m1)))):
                    v = vertices[a]

                    if ((np.dot(n1, normalize(v - vp2)) > -epsilon) and \
                        (np.dot(n2, normalize(v - vm1)) > -epsilon) and \
                        (np.dot(n3, normalize(v - vp1)) > -epsilon)):
                        positive = False
                        break


        # Negative sided triangle
        n1 = np.cross(normal, normalize(vm2 - vp1))

        if (np.dot(n1, vm1 - vp1) > epsilon):
            negative = True
            n2 = np.cross(normal, normalize(vm1 - vm2))
            n3 = np.cross(normal, normalize(vp1 - vm1))

            for a in  range(vertexCount - 1):
                # Look for more vertices inside triangle
                if (active[a] and (a != m1 and (a != m2 and (a != p1)))):
                    v = vertices[a]

                    if ((np.dot(n1, normalize(v - vp1)) > -epsilon) and \
                        (np.dot(n2, normalize(v - vm2)) > -epsilon) and \
                        (np.dot(n3, normalize(v - vm1)) > -epsilon)):
                        negative = False
                        break

        # If both triangles are valid, then choose the one having the larger
        # yet smallest angle
        if (positive and negative):
            pd = np.dot(normalize(vp2 - vm1), normalize(vm2 - vm1))
            md = np.dot(normalize(vm2 - vp1), normalize(vp2 - vp1))

            if(np.abs(pd - md) < epsilon):
                if (lastPositive):
                    positive = False
                else:
                    negative = False
            else:
                if(pd < md):
                    negative = False
                else:
                    positive = False

        if positive:
            # Output the triangle m1, p1, p2.
            active[p1] = False
            t = np.array([m1, p1, p2])
            triangleIndices.append(t)
            triangleCount = triangleCount + 1

            p1 = getNextActive(p1, vertexCount, active)
            p2 = getNextActive(p2, vertexCount, active)
            lastPositive = True

            start = -1

        elif negative:
            # Output the triangle m2, m1, p1.
            active[m1] = False
            t = np.array([m2, m1, p1])
            triangleIndices.append(t)
            triangleCount = triangleCount + 1

            m1 = getPrevActive(m1, vertexCount, active)
            m2 = getPrevActive(m2, vertexCount, active)
            lastPositive = False

            start = -1

        else:
            # Exit if we've gone all the way around the
            # polygon without finding a valid triangle.
            if start == -1:
                start = p2
            elif p2 == start:
                break

            # Advance working set of vertices.
            m2 = m1
            m1 = p1
            p1 = p2
            p2 = getNextActive(p2, vertexCount, active)

    # return Triangle points
    triangles = []
    for i in range(len(triangleIndices)):
        triangle = []
        for j in range(3):
            triangle.append(vertices[triangleIndices[i][j]])
        triangles.append(triangle)

    return      

def drawTriangle(points, ax):
    for i in range(3):
        ax.plot([points[i][0], points[(i+1)%3][0]], \
                [points[i][1], points[(i+1)%3][1]], \
                [points[i][2], points[(i+1)%3][2]])


if __name__ == '__main__':
    # 2D

    # 3D
    # Polygon
    # Rectangle
    width = 10
    length = 10

    p0 = np.array([0, 0, 0])
    p1= np.array([0, 0, width])
    p2 = np.array([0, length, width])
    p3 = np.array([0, length, 0])

    Vertices = []

    Vertices.append(p0)
    Vertices.append(p1)
    Vertices.append(p2)
    Vertices.append(p3)

    normal = computeNormal(p0, p1, p2)
    center = np.array([0, length/2, width/2])
    normal = normal + center

    # triangles = Triangulate(Vertices, normal)
    triangles = Triangulate(Vertices)

    fig = plt.figure()
    ax = plt.axes(projection='3d')

    ax.plot([center[0], normal[0]], \
            [center[1], normal[1]], \
            [center[2], normal[2]])

    for i in range(4):
        ax.plot([Vertices[i][0], Vertices[(i+1)%4][0]], \
                [Vertices[i][1], Vertices[(i+1)%4][1]], \
                [Vertices[i][2], Vertices[(i+1)%4][2]])

    plt.show()

    fig = plt.figure()
    ax = plt.axes(projection='3d')

    # Plot Triangles
    for i in range(len(triangles)):
        drawTriangle(triangles[i], ax)

    plt.show()
