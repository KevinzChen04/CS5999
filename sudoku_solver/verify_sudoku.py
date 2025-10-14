#!/usr/bin/env python3
"""
Verify the Sudoku input by displaying it in a grid format
"""

def read_and_display_sudoku(filename):
    """Read input and display the Sudoku grid"""
    with open(filename, 'r') as f:
        lines = f.readlines()
    
    num_givens = int(lines[0].strip())
    print(f"Number of given values: {num_givens}")
    
    # Create empty 9x9 grid
    grid = [[0 for _ in range(9)] for _ in range(9)]
    
    # Fill in the given values
    for i in range(1, num_givens + 1):
        parts = lines[i].strip().split()
        row = int(parts[0]) - 1  # Convert to 0-indexed
        col = int(parts[1]) - 1  # Convert to 0-indexed
        value = int(parts[2])
        grid[row][col] = value
    
    # Display the grid
    print("\nSudoku Grid (0 = empty):")
    print("+" + "-" * 21 + "+")
    for i in range(9):
        print("|", end="")
        for j in range(9):
            if j % 3 == 0 and j > 0:
                print("|", end="")
            if grid[i][j] == 0:
                print(" .", end="")
            else:
                print(f" {grid[i][j]}", end="")
        print(" |")
        if (i + 1) % 3 == 0 and i < 8:
            print("+" + "-" * 21 + "+")
    print("+" + "-" * 21 + "+")
    
    return grid

if __name__ == "__main__":
    read_and_display_sudoku("input.txt")
