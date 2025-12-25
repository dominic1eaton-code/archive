"""
	@file		: InfoMaps.py
	@author		:
	@description:
"""

# Imports
import bpy 
import bmesh 

from Triangulation import Triangulation 

class InfoMap():
	def __init__(self, settings):
		self.dimensions = settings['dimensions']
		self.values = []
		
	def generateValues(self):
		return None
		
	def getValues(self):
		return self.values
	
	
class HeightMap(InfoMap):
	pass
	
class PopulationMap(InfoMap):
	pass
