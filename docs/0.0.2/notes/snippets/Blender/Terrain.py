"""
	@file		: Terrain.py
	@author		:
	@description:
"""

# Imports
import random 
import numpy as np


class Terrain():
	def __init__(self, settings):
		self.dimensions = settings['dimensions']
		self.maps = []
		
	def addMap(self, map):
		self.map.append(map)
		return None
		
	def getValues(self):
		return self.values
	