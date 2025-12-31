"""
    @File       : LLC.py
    @Author     : eatondo
    @Description:
"""

# Imports
import numpy as np


# @brief    Low Level Controller
class LLC:
    def __init__(self):
        z = 0

    def execute(self):
        acceleration = self.Throttle()
        brake = self.Brake()
        steering = self.Steering()
        Dynamics = [acceleration, brake, steering]
        return Dynamics

    def Throttle(self):
        return None

    def Brake(self):
        return None

    def Steering(self):
        return None
