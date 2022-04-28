# Clique

A subset of vertices $S$ in a graph $G = (V, E)$ is a __clique__ if every distinct pair of vertices of $S$ is connected.

A __maximum clique__ is an clique of largest possible size. This size is called the clique number of $G$ and is usually denoted by $\omega(G)$.

A __clique clover__ or __partition into cliques__ is a partition of the vertices of the graph into cliques.

A __minimum clique cover__ is a clique cover with the smallest possible number of cliques. This number is called the __clique cover number__ of the graph.



## Clique search and decision problem


The clique decision problem consists in deciding whether a graph, given a natural integer $k$, has a clique of size $k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The clique search problem consists in finding such a clique.

Finding a clique of size $k$ is equivalent to finding an [independent set](../indset#independent-set-decision-problem) of size $k$ in the graph's complement. 

## Maximum clique problem and clique number

The maximum clique problem consists in finding a maximum clique in the graph; it is  NP-hard.

Finding a maximum clique is equivalent to finding a [maximum independent set](../indset#maximum-independent-set-problem) in the graph's complement.

Computing the clique number of a graph is also NP-hard. It is equal to the [independence number](../indset#independence-number) of the graph's complement.

## Clique cover search and decision problem


The clique cover decision problem consists in deciding whether a graph, given a natural integer $k$, has a clique cover of size $k$. This problem has been proven to be NP-complete (Karp, 1972) [1].The clique cover search problem consists in finding such a clique.

Finding a clique cover of size $k$ is equivalent to finding a [k-coloring](../coloring#k-coloring-problem) in the graph's complement. 

## Minimum clique cover problem and clique cover number

The minimum clique cover problem consists in finding a minimum clique cover in the graph; it is  NP-hard.

Finding a mininum clique cover is equivalent to finding a [minimum coloring](../coloring#minimum-coloring-problem) in the graph's complement.

Computing the clique cover number of a graph is also NP-hard. It is equal to the [chromatic number](../coloring#chromatic-number) of the graph's complement.

---


[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.
