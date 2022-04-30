# N-Queens Puzzle

The __n-queens puzzle__ consists in placing $n$ queens on a $n \times n$ chess board, such that no two queens are on the same row, column or diagonal. Although the decision and the search problem are decidable in polynomial time, some of its variants are known to be NP-complete.

## N-Queens completion problem

The n-queens completion decision problem consists in, given a set $Q$ of queens already placed on the board, deciding whether the assignment can be completed. This problem has been proven to be NP-complete [1]. The search version of the problem consists in finding such a (partial) assignment.

Finding a solution for the n-queens completion problem is equivalent to find a feasible solution to this 0-1 integer linear program:

N queens must be placed on the board:

$$ \sum_{i = 0}^{n-1}\sum_{j = 0}^{n-1} x_{ij} = n$$

There is at most one queen on each row and column:

$$ \sum_{i = 0}^{n-1} x_{ij} \leq 1 \ \forall j = 0, ..., n-1$$

$$ \sum_{j = 0}^{n - 1} x_{ij} \leq 1 \ \forall i = 0, ..., n-1$$

There is at most one queen on each diagonal:

$$ \sum_{i = 0}^n 1_{0 \leq j - i < n} x_{(n-1-i)(j-i)} \leq \ \forall j = 0, ..., 2n - 2$$

$$ \sum_{j = 0}^n 1_{0 \leq i - j < n} x_{j(i - j)} \leq \ \forall i = 0, ..., 2n - 2$$

The queens in $Q$ must be placed:

$$ x_{ij} = 1 \  \forall (i, j) \in Q$$

## Blocked n-Queens Problem

The blocked n-queens decision problem consists in, given a set $X$ of cells where the queens cannot be placed, deciding whether the $n$ queens can be placed on the board. This problem has been proven to be NP-complete [1]. The search version of the problem consists in finding such an assignment.

Finding a solution for the blocked n-queens problem is equivalent to find a feasible solution to this 0-1 integer linear program:

N queens must be placed on the board:

$$ \sum_{i = 0}^{n-1}\sum_{j = 0}^{n-1} x_{ij} = n$$

There is at most one queen on each row and column:

$$ \sum_{i = 0}^{n-1} x_{ij} \leq 1 \ \forall j = 0, ..., n-1$$

$$ \sum_{j = 0}^{n - 1} x_{ij} \leq 1 \ \forall i = 0, ..., n-1$$

There is at most one queen on each diagonal:

$$ \sum_{i = 0}^n 1_{0 \leq j - i < n} x_{(n-1-i)(j-i)} \leq \ \forall j = 0, ..., 2n - 2$$

$$ \sum_{j = 0}^n 1_{0 \leq i - j < n} x_{j(i - j)} \leq \ \forall i = 0, ..., 2n - 2$$

The cells in $X$ cannot be occupied:

$$ x_{ij} = 0 \  \forall (i, j) \in X$$


---

[1] Ian P. Gent, Christopher Jefferson, and Peter Nightingale
Complexity of n-Queens Completion
JAIR, 2017 

