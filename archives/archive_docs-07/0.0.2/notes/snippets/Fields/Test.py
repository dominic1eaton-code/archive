import numpy as np

def normalize(v):
    norm = np.linalg.norm(v)
    if norm == 0:
       return v
    return v / norm

def CubicInterp(t, P1, P2, T1, T2):
    # Hermite Curve coefficients
    a = 2*t**3 - 3*t**2 + 1
    b = t**3 - 2*t**2 + t
    c = t**3 - t**2
    d = -2*t**3 + 3*t**2

    h = a*P1 + b*T1 + c*T2 + d*P2

    # return hermite curve point at parametric value t
    return h

def DerivCubicInterp(t, P1, P2, T1, T2):
    # Derivative Hermite Curve coefficients
    t2 = t * t

    a = (6 * t2) - (6 * t);
    b = 3 * t2 - 4 * t + 1;
    c = 3 * t2 - 2 * t;
    d = -6 * t2 + 6 * t;

    h = a*P1 + b*T1 + c*T2 + d*P2

    # return hermite curve point at parametric value t
    return h

def Test():
    length = 1000

    p0 = np.array([0, 0, 0])
    p1 = np.array([0, length, 0])

    t0 = np.array([0, 0, 1000])
    t1 = np.array([0, 0, 500])

    # Calculate spline points
    # t = 0

    Points  = []
    dPoints = []
    Nz = np.array([1, 0, 0])
    result = []
    width = 200
    nPoints = 4
    step = int(length / nPoints)

    for t in range(0, length, step):
        Points.append(CubicInterp(t, p0, p1, t0, t1))
        dPoints.append(DerivCubicInterp(t, p0, p1, t0, t1))

        Nx = normalize(DerivCubicInterp(t, p0, p1, t0, t1))
        Ny = np.cross(Nx, Nz) * width/2
        result.append(Ny)

    for i in range(len(Points)):
        print("POINTS: ")
        print(normalize(Points[i]))
        print(normalize(dPoints[i]))

    for i in range(len(result)):
        print("RESULTS: ")
        print(result[i])





if __name__ == '__main__':
    Test()