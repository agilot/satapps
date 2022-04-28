# Hamiltonian graphs

Given a directed graph $G = (V, E)$, a __Hamiltonian path__ is a path that visits each vertex exactly once. A __Hamiltonian cycle__ (or __Hamiltonian circuit__) is a Hamiltonian path that is a cycle.



## Hamiltonian cycle search and decision problem

The Hamiltonian cycle decision problem consists in deciding whether a Hamiltonian path exists in the graph. This problem has been proven to be NP-complete (Karp, 1972) [1]. The search version of the problem consists in finding such a cycle.

__If the graph is connected and__ $\textbf{|V| > 2}$ (if it is not the case there is no such cycle), finding a Hamiltonian cycle is equivalent to find a feasible solution to this 0-1 integer linear program:


$$ \sum_{e \in \delta^+(u)} x_e = 1 \ \forall u \in V $$

$$ \sum_{e \in \delta^-(u)} x_e = 1 \ \forall u \in V $$


That is, the Hamiltonian cycle problem is a special case of the [traveling salesperson decision problem](#traveling-salesperson-problem) where all the weights are equal to 1 and the cost $|V|$.

## Hamiltonian path search and decision problem

The Hamiltonian path decision problem consists in deciding whether a Hamiltonian path exists in the graph. This problem has been proven to be NP-complete [2]. The search version of the problem consists in finding such a path.

Finding a Hamiltonian path is equivalent to connect a new vertex to all the vertices in the graph and search for a Hamiltonian cycle in this new graph.

## Traveling salesperson problem search decision problem

The traveling salesperson problem consists in deciding whether, given a cost $C$, a Hamiltian cycle with weigth smaller or equal than $C$ exists in the graph. This problem is NP-complete (Proof 1).

> __Proof 1__
>
> TSP is NP-hard since it is a generalization of the Hamiltonian cycle problem. However, it remains in NP as either the graph is not connected (polynomially checkable) and the problem has no solution, or the graph is connected in which case the problem is reducible to a 0-1 linear integer program.

__If the graph is connected and__ $\textbf{|V| > 2}$ (if it is not the case there is no such cycle), finding a Hamiltonian cycle is equivalent to find a feasible solution to this 0-1 integer linear program:


$$ \sum_{e \in \delta^+(u)} x_e = 1 \ \forall u \in V $$

$$ \sum_{e \in \delta^-(u)} x_e = 1 \ \forall u \in V $$

$$ \sum_{e \in E} w_e x_e \leq C$$

---
[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2] M.R. Garey and M.R. Johnson. Computers and Intractability. Freeman, New
York, 1979.