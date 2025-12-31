import bpy
import bmesh
import numpy as np
import time


from bpy.props import (
        BoolProperty,
        BoolVectorProperty,
        FloatProperty,
        FloatVectorProperty,
        )


class AddBox(bpy.types.Operator):