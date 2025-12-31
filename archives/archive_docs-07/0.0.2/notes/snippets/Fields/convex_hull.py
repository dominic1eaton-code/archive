"""
    @file       :
    @author     :
    @description:

    @see https://www.oreilly.com/ideas/an-elegant-solution-to-the-convex-hull-problem
"""
import numpy as np
import matplotlib.pyplot as plt


# 2D Convex Hull
def split(u, v, points):
    # return points on left side of UV
    return [p for p in points if np.cross(p - u, v - u) < 0]

def extend(u, v, points):
    if not points:
        return []

    # find furthest point W, and split search to WV, UW
    w = min(points, key=lambda p: np.cross(p - u, v - u))
    p1, p2 = split(w, v, points), split(u, w, points)
    return extend(w, v, p1) + [w] + extend(u, w, p2)

def convex_hull(points):
    # find two hull points, U, V, and split to left and right search
    u = min(points, key=lambda p: p[0])
    v = max(points, key=lambda p: p[0])
    left, right = split(u, v, points), split(v, u, points)

    # find convex hull on each side
    return [v] + extend(u, v, left) + [u] + extend(v, u, right) + [v]

# results
points = np.random.rand(100, 2)
hull = np.array(convex_hull(points))

# plot
plt.scatter(x=points[:, 0], y=points[:, 1])
plt.plot(hull[:, 0], hull[:, 1], linewidth=3, color='red')
plt.show()
