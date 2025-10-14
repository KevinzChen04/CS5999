#!/usr/bin/env python3
"""
Sudoku Solver using Microsoft Z3
Reads input from input.txt file and solves the Sudoku puzzle.
"""

from z3 import *
import sys

def read_input(filename):
    """
    Read Sudoku input from file.
    Format:
    - First line: number of given spots
    - Following lines: row col value (1-indexed)
    """
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
        
        num_givens = int(lines[0].strip())
        givens = []
        
        for i in range(1, num_givens + 1):
            parts = lines[i].strip().split()
            row = int(parts[0]) - 1  # Convert to 0-indexed
            col = int(parts[1]) - 1  # Convert to 0-indexed
            value = int(parts[2])
            givens.append((row, col, value))
        
        return givens
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading input file: {e}")
        sys.exit(1)

def create_sudoku_solver():
    """
    Create Z3 solver for 9x9 Sudoku puzzle.
    """
    # Create 9x9 grid of integer variables
    cells = [[Int(f"cell_{i}_{j}") for j in range(9)] for i in range(9)]
    
    solver = Solver()
    
    # Each cell must be between 1 and 9
    for i in range(9):
        for j in range(9):
            solver.add(And(cells[i][j] >= 1, cells[i][j] <= 9))
    
    # Each row must contain all digits 1-9
    for i in range(9):
        solver.add(Distinct([cells[i][j] for j in range(9)]))
    
    # Each column must contain all digits 1-9
    for j in range(9):
        solver.add(Distinct([cells[i][j] for i in range(9)]))
    
    # Each 3x3 box must contain all digits 1-9
    for box_row in range(3):
        for box_col in range(3):
            box_cells = []
            for i in range(3):
                for j in range(3):
                    box_cells.append(cells[box_row * 3 + i][box_col * 3 + j])
            solver.add(Distinct(box_cells))
    
    return solver, cells

def solve_sudoku(givens):
    """
    Solve Sudoku puzzle with given constraints.
    """
    solver, cells = create_sudoku_solver()
    for row, col, value in givens:
        solver.add(cells[row][col] == value)
    
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(9):
            row = []
            for j in range(9):
                row.append(model[cells[i][j]].as_long())
            solution.append(row)
        return solution
    else:
        return None

def print_sudoku(solution):
    """
    Print the Sudoku solution in a readable format.
    """
    if solution is None:
        print("No solution found!")
        return
    
    print("Sudoku Solution:")
    print("+" + "-" * 23 + "+")
    for i in range(9):
        print("|", end="")
        for j in range(9):
            if j % 3 == 0 and j > 0:
                print(" |", end="")
            print(f" {solution[i][j]}", end="")
        print(" |")
        if (i + 1) % 3 == 0 and i < 8:
            print("+" + "-" * 23 + "+")
    print("+" + "-" * 23 + "+")

def main():
    """
    Main function to solve Sudoku from input file.
    """
    input_file = "input.txt"

    givens = read_input(input_file)
    solution = solve_sudoku(givens)
    
    if solution:
        print("\nSolution found!")
        print_sudoku(solution)
    else:
        print("\nNo solution exists for this Sudoku puzzle.")

if __name__ == "__main__":
    main()
