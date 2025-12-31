import plotly.plotly as py
import plotly.graph_objs as go
from plotly.tools import FigureFactory as FF
from scipy import interpolate

import numpy as np
import pandas as pd
import scipy

x = np.arange(-5.0, 5.0, 0.25)
y = np.arange(-5.0, 5.0, 0.25)
xx, yy = np.meshgrid(x, y)
z = np.sin(xx**2+yy**2)
f = interpolate.interp2d(x, y, z, kind='cubic')

xnew = np.arange(-5.0, 5.0, 1e-1)
ynew = np.arange(-5.0, 5.0, 1e-1)
znew = f(xnew, ynew)

trace1 = go.Scatter3d(
    x=x,
    y=y,
    z=z[0, :],
    mode='markers',
    name='Data',
    marker = dict(
        size = 7
    )
)

trace2 = go.Scatter3d(
    x=ynew,
    y=xnew,
    z=znew[0, :],
    marker=dict(
        size=3,
    ),
    name='Interpolated Data'
)

layout = go.Layout(
    title='Interpolation and Extrapolation in 2D',
    scene=dict(
            camera= dict(
                up=dict(x=0, y=0, z=1),
                center=dict(x=0, y=0, z=0),
                eye=dict(x=1, y=-1, z=0)
            )
    )
)

data = [trace1, trace2]

fig = go.Figure(data=data, layout=layout)
py.iplot(fig, filename='interpolation-and-extrapolation-2d')