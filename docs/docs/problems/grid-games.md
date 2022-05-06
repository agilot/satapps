# Grid Games

## Latin square completion

The latin square is a game where the player needs to fill a $n \times n$ grid with integers between 1 and $n$, each occuring exactly once in each row and each column. Determining whether a latin square has a solution, given a list of cells already filled, is NP-complete [1].

## Generalised Sudoku completion

Sudoku is a game where the player needs to fill a $9 \times 9$ grid with integers between 1 and $9$, each occuring exactly once in each row and each column. Furthermore, th grid is divided in 9 $3 \times 3$ square yielding the additional constraint that all the number inside a square must be distinct. Generalised Sudoku is  the same game with a grid of $k^2 \times k^2$, numbers going from 1 to $k^2$ and $k^2$ squares of size $k \times k$ instead. Determining whether a generalised Sudoku grid has a solution, given a list of cells already filled, is NP-complete [2].


---

[1] Charles J. Colbourn, The complexity of completing partial Latin squares, Discrete Applied Mathematics, Volume 8, Issue 1, 1984, Pages 25-30.

[2] Complexity and completeness of finding another solution and its application to puzzles
T. Yato and T. Seta, IEICE Trans. Fundam. Electron., E86-A (5) (2003), pp. 1052-1060.