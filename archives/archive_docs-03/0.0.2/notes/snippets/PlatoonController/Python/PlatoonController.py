"""
    @File       : LLC.py
    @Author     : eatondo
    @Description:
"""

# Imports
import numpy as np
from PLC import PLC
from HLC import HLC
from LLC import LLLC


# @brief    Complete Platoon Controller
class PlatoonController:
    def __init__(self):
        PlatoonLevelController = PLC()
        HighLevelController = PLC()
        LowLevelController = PLC()


    def Execute(self, Data):
        Objectives = self.PlatoonLevelController.execute(Data)
        Manuevers = self.HighLevelController.execute(Objectives)
        Dynamics = self.LowLevelController.execute(Manuevers)
        return Dynamics

