#!/usr/bin/env python

# Copyright (c) 2015 Xi Wang
#
# This file is part of the UW CSE 551 lecture code.  It is freely
# distributed under the MIT License.

"""
This resembles Section 2.4 of the DART paper (PLDI'05).
"""

import sys
import io
import re
from collections import defaultdict
from mc import *

def popcount(x):
  if x == 0:
    return 0
  return popcount(x >> 1) + (x & 1)

def test_me(x):
  if (x > 0):
    assert(popcount(x) < x) 

def parse_trace(lines):
  """Parse the trace and build parent-child relationships."""
  children = defaultdict(list)
  nodes = defaultdict(list)
  root = None
  
  # First pass: collect all actions for each PID
  for line in lines:
    match = re.match(r'\[(\d+)\]\s+(.+)', line.strip())
    if match:
      pid = int(match.group(1))
      action = match.group(2).strip()
      nodes[pid].append(action)
      if root is None:
        root = pid
  
  # Second pass: build parent-child relationships
  seen_pids = set()
  active_stack = []
  
  for line in lines:
    match = re.match(r'\[(\d+)\]\s+(.+)', line.strip())
    if match:
      pid = int(match.group(1))
      action = match.group(2).strip()
      
      if pid not in seen_pids:
        seen_pids.add(pid)
        if active_stack:
          parent = active_stack[-1]
          children[parent].append(pid)
        active_stack.append(pid)
      
      if action in ['exit', 'unreachable']:
        if pid in active_stack:
          active_stack.remove(pid)
  
  return root, children, nodes

def print_tree(pid, children, nodes, prefix="", is_last=True):
  """Print the tree recursively."""
  actions = nodes.get(pid, [])
  
  connector = "└── " if is_last else "├── "
  
  if actions:
    print(f"{prefix}{connector}[{pid}] {actions[0]}")
    
    extension = "    " if is_last else "│   "
    for action in actions[1:]:
      print(f"{prefix}{extension}     {action}")
  else:
    print(f"{prefix}{connector}[{pid}]")
  
  child_list = children.get(pid, [])
  extension = "    " if is_last else "│   "
  
  for i, child in enumerate(child_list):
    is_last_child = (i == len(child_list) - 1)
    print_tree(child, children, nodes, prefix + extension, is_last_child)

if __name__ == "__main__":
  import subprocess
  import os
  import tempfile
  
  # Check if we should just run the test (for subprocess call)
  if '--run-test' in sys.argv:
    x = BitVec("x", 4)
    test_me(x)
  else:
    # Run the test and capture output
    temp_file = tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix='.txt')
    temp_file.close()
    
    try:
      # Run this script with --run-test flag and capture output
      result = subprocess.run(
        [sys.executable, __file__, '--run-test'],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(os.path.abspath(__file__)) or '.'
      )
      
      # Combine stdout and stderr
      output = result.stdout + result.stderr
      lines = output.strip().split('\n')
      
      # Filter out only the process trace lines
      trace_lines = [line for line in lines if re.match(r'\[\d+\]', line)]
      
      # Print the tree visualization
      print("Process Tree Visualization")
      print("=" * 60)
      print()
      
      if trace_lines:
        root, children, nodes = parse_trace(trace_lines)
        
        if root:
          print_tree(root, children, nodes)
        else:
          print("No processes found in trace.")
      else:
        print("No process traces found.")
      
      print()
      print("=" * 60)
      if trace_lines:
        root, children, nodes = parse_trace(trace_lines)
        print(f"Total processes: {len(nodes)}")
      
      # Also print any errors/tracebacks
      error_lines = [line for line in lines if not re.match(r'\[\d+\]', line) and line.strip()]
      if error_lines:
        print()
        print("Additional output:")
        for line in error_lines:
          print(line)
        print("-" * 60)
    finally:
      # Clean up temp file
      if os.path.exists(temp_file.name):
        os.unlink(temp_file.name)
