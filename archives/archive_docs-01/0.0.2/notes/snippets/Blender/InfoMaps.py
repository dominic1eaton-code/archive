"""
	@file		: InfoMaps.py
	@author		:
	@description:
"""

# Imports
import bpy 
import bmesh 

from Triangulation import Triangulation 
from Noise import *

class BaseMap():
	def __init__(self, settings):
		self.dimensions = settings['dimensions']
		self.values = []
		
	def generateValues(self):
		return None
		
	def getValues(self):
		return self.values
	
	
class HeightMap(BaseMap):
	pass
	
class PopulationMap(BaseMap):
	pass
