"""
	@file		: TerrainMesh.py
	@author		:
	@description:
"""

# Imports
import bpy 
import bmesh 

from Mesh import BaseMesh
from Triangulation import Triangulation 

class TerrainMesh(BaseMesh):
	# Properties
	# Blender 
	bl_idname = "mesh.primitve_add_mesh"
	bl_label = "Add Mesh"
	bl_options = {'REGISTER', 'UNDO'}
	
	def __init__(self, settings, options):
		# Initialization
		self.resolution = settings['resolution']
		self.components = settings['components']
		self.sections = []
		self.quads = [] 
		self.vertices = []
		self.faces = []
		
		
	def generateVerts(self):
		raise NotImplementedError("Subclass must implement abstract method")

	def generateTriangles(self):
		pass
		
	def generateFaces(self, verts):
		triangles = Triangulate(verts) 

	def scaleVerts(self, verts, dimensions):
		scale = []
		return Verts 
		
	def execute(self, context):
		# Create new mesh 
		dimensions = {
			'width' : self.width,
			'height': self.height,
			'depth' : self.depth,
		}
		
		verts, faces = createMesh(dimensions)
		mesh = bpy.data.meshes.new("Box")
		bm = bmesh.new()
		
		# generate mesh geometry
		for v_co in verts:
			bm.verts.new(v_co)

		bm.verts.ensure_lookup_table()
		for f_idx in faces:
			bm.faces.new([bm.verts[i] for i in f_idx])

		bm.to_mesh(mesh)
		mesh.update()

		# add the mesh as an object into the scene with this utility module
		from bpy_extras import object_utils
		object_utils.object_data_add(context, mesh, operator=self)

		return {'FINISHED'}
		

def menu_func(self, context):
	self.layout.operator(AddBox.bl_idname, icon='MESH_CUBE')


def register():
	bpy.utils.register_class(AddBox)
	bpy.types.INFO_MT_mesh_add.append(menu_func)


def unregister():
	bpy.utils.unregister_class(AddBox)
	bpy.types.INFO_MT_mesh_add.remove(menu_func)
