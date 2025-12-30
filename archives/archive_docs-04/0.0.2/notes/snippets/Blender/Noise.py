"""
	@file		: Noise.py
	@author		:
	@description:
"""

# Imports
import random 
import numpy as np

from Triangulation import Triangulation 

options = {'size': 10,
	   'resolution': 10,}

class BaseNoise():
	def __init__(self, settings={'dimensions': 2, 
					 'octaves'	 : 2, 
					 'tile'		 : (),
					 'bias'	 : False, 
					 'frequency0': 0.1}):
		# Initialization
		self.dimensions = settings['dimensions']
		self.octaves = settings['octaves']
		self.tile = settings['tile'] + (0,) * dimension
		self.unbias = settings['unbias']
		self._values = []
		
	def generateValues(self):
		return None
		
	def getValues(self):
		return self.values
	
	def __call__(self):
		pass 
		
	def _generateGrad(self):
		pass 
		
	def _lerp(self, a, b, t):
		return a + t * (b - a)
	
	
class PerlinNoise(BaseNoise):
	def __init__(self):
		pass

class SimplexNoise(BaseNoise):
	def __init__(self):
	
class FractalNoise(BaseNoise):
	def __init__(self):
		pass		pass
		
class SimplexNoise(BaseNoise):
	def __init__(self):
		pass

class PinkNoise(BaseNoise):
	def __init__(self):
		pass

class BlueNoise():
	def __init__(self):
		pass
