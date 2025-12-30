import numpy as np
import matplotlib.pyplot as plt
from Streamlines import Streamlines

if __name__ == "__main__":
    w = 3
    Y, X = np.mgrid[-w:w:100j, -w:w:100j]
    angle = 5 / 8
    theta = (np.pi * angle)
    U = np.ones(X.shape) * np.cos(-2 * theta)
    V = np.ones(Y.shape) * np.sin(-2 * theta)

    streamlines = Streamlines(X, Y, U, V)
    ax = streamlines.plot()
    ax.set_title("Streamlines")
    plt.show()