"""
    @File       :
    @Author     : eatondo
    @Description:
"""

# Imports
import numpy as np
from SocialPLC import SocialPLC
from StructuredPLC import StructuredPLC
from CommandPLC import CommandPLC

# @brief    Platoon Level Controller
class PLC:
    def __init__(self):
        SocialController = SocialPLC()
        StructuredController = StructuredPLC()
        CommandController = CommandPLC()

    # @brief        Perform Platoon Control Algorithm
    # @param
    # @return
    def execute(self, I, Pp):
        Ir = self.Recognize(I, Pp)
        Is = self.Sustain(Ir)
        Ip = self.Predict(Is)
        return Ip


    # RECOGNITION
    # @brief        Perform Platoon Recognition
    # @param
    # @param
    # @param
    # @return       the estimated platoon state Pr
    def Recognize(self, I, Pp):
        vstate = self.vEstimate()
        Pm = self.Identify()
        Ip = self.Estimate()
        Ipp = self.Filter()
        Pr = [Pm, Ipp]
        return Pr

    def vEstimate(self):
        return None

    def Identify(self):
        return None

    def Estimate(self):
        return None

    def Filter(self):
        return None


    # SUSTAINABILITY
    # @brief        Perform Platoon Sustainability
    # @param
    # @param
    # @param
    # @return       the sustainable platoon state Ps
    def Sustain(self, Pr):
        O_g = self.GlobalObjective()
        O_l = self.LocalObjective()
        O_s = self.SafetyObjective()

        Ps = self.Decider([O_g, O_l, O_s])
        return Ps

    def GlobalObjective(self):
        Ff = self.Flock()
        Fc = self.Crowd()
        u_crowd = Ff + Fc
        return u_crowd

    def LocalObjective(self):
        Ff = self.Interest()
        Fc = self.Survive()
        u_vehicle = Ff + Fc
        return u_vehicle

    def SafetyObjective(self):
        Ff = self.Danger()
        Fc = self.Adversary()
        u_safety = Ff + Fc
        return u_safety

    def Decider(self, Objectives):
        O = Objectives
        return O

    # PREDICTION
    # @brief        Perform Platoon Prediction
    # @param
    # @param
    # @param
    # @return       the sustainable platoon state Pp
    def Predict(self, Ps):
        Pp = 0
        return Pp
