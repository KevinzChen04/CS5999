#!/usr/bin/env python

# Copyright (c) 2015 Xi Wang
#
# This file is part of the UW CSE 551 lecture code.  It is freely
# distributed under the MIT License.

"""
This resembles Section 2.4 of the DART paper (PLDI'05).
"""

from mc import *

def popcount(x):
  if x == 0:
    return 0
  return popcount(x >> 1) + (x & 1)

def test_me(x):
  assert(popcount(x) < x) 
  

x = BitVec("x", 4)
test_me(x)
