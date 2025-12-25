import bpy
import bmesh
import numpy as np
import time

from test_perlin import perlin

from bpy.props import (
        BoolProperty,
        BoolVectorProperty,
        FloatProperty,
        FloatVectorProperty,
        )


class AddBox(bpy.types.Operator):
    """Add a simple box mesh"""
    bl_idname = "mesh.primitive_box_add"
    bl_label = "Add Box"
    bl_options = {'REGISTER', 'UNDO'}

    width = FloatProperty(
            name="Width",
            description="Box Width",
            min=0.01, max=100.0,
            default=1.0,
            )
    height = FloatProperty(
            name="Height",
            description="Box Height",
            min=0.01, max=100.0,
            default=1.0,
            )
    depth = FloatProperty(
            name="Depth",
            description="Box Depth",
            min=0.01, max=100.0,
            default=1.0,
            )
    layers = BoolVectorProperty(
            name="Layers",
            description="Object Layers",
            size=20,
            options={'HIDDEN', 'SKIP_SAVE'},
            )

    # generic transform props
    view_align = BoolProperty(
            name="Align to View",
            default=False,
            )
    location = FloatVectorProperty(
            name="Location",
            subtype='TRANSLATION',
            )
    rotation = FloatVectorProperty(
            name="Rotation",
            subtype='EULER',
            )

    def __init__(self):
        print('hello')

    def execute(self, context):
        verts_loc, faces = self.add_box(self.width,
                                   self.height,
                                   self.depth,
                                   )

        mesh = bpy.data.meshes.new("Box")

        bm = bmesh.new()

        for v_co in verts_loc:
            bm.verts.new(v_co)

        bm.verts.ensure_lookup_table()
        #for f_idx in faces:
        #    bm.faces.new([bm.verts[i] for i in f_idx])

        bm.to_mesh(mesh)
        mesh.update()

        # add the mesh as an object into the scene with this utility module
        from bpy_extras import object_utils
        object_utils.object_data_add(context, mesh, operator=self)

        return {'FINISHED'}


    def add_box(self, width, height, depth):
        """
        This function takes inputs and returns vertex and face arrays.
        no actual mesh data creation is done here.
        """
        s = 60
        numi = s
        numj = s

        x = +1.0
        y = -1.0
        z = -1.0

        faces = []
        verts = []

        """
        verts = [(x, x, z),
                 (x, y, z),
                 (y, y, z),
                 (y, x, z),]


        t1 = (0,1,2)
        t2 = (2,3,0)
        faces = [t1, t2]
        """

        t1 = (0,1,2)
        t2 = (2,3,0)

        k = 1.0

        lin = np.linspace(0,5,s,endpoint=False)
        xx,yy = np.meshgrid(lin,lin) # FIX3: I thought I had to invert x and y here but it was a mistake
        noise = perlin(xx,yy,seed=int(time.time()))
        noisep = noise
        #noisep *= 255.0/noise.max()
        noisep += noisep.mean()

        w = 0
        for i in range(numi):
            for j in range(numj):
                verts.append((x+2*i, x+2*j, z*noisep[i, j]))
                verts.append((x+2*i, y+2*j, z*noisep[i, j]))
                verts.append((y+2*i, y+2*j, z*noisep[i, j]))
                verts.append((y+2*i, x+2*j, z*noisep[i, j]))
                faces.append((0+w,1+w,2+w))
                faces.append((2+w,3+w,0+w))
                w += 4

        # apply size
        for i, v in enumerate(verts):
            verts[i] = v[0] * width, v[1] * depth, v[2] * height

        return verts, faces


def menu_func(self, context):
    self.layout.operator(AddBox.bl_idname, icon='MESH_CUBE')


def register():
    bpy.utils.register_class(AddBox)
    bpy.types.INFO_MT_mesh_add.append(menu_func)


def unregister():
    bpy.utils.unregister_class(AddBox)
    bpy.types.INFO_MT_mesh_add.remove(menu_func)

if __name__ == "__main__":
    register()

    # test call
    bpy.ops.mesh.primitive_box_add()
