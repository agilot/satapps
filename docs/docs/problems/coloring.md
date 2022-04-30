# Coloring

Given a graph $G = (V, E)$, a __vertex coloring__ is an assignment such that no two adjacent vertices are of the same color. This is equivalent to partionning $V$ into [independent sets](../indset).

A vertex coloring that minimizes the number of colors needed for a given graph G is known as a __minimum vertex coloring__ of G. The minimum number of colors itself is called the __chromatic number__, denoted $\chi(G)$.

An __edge coloring__ is an assignment such that no two adjacent edges are of the same color. This is equivalent to partionning $V$ into disjoint matchings.

An edge coloring that minimizes the number of colors needed for a given graph G is known as a __minimum edge coloring__ of G. The minimum number of colors itself is called the __chromatic index__, denoted $\chi'(G)$.


## k-coloring problem


The k-coloring problem consists in deciding whether a graph, given a natural integer $k$, admits a k-coloring. This problem has been proven to be NP-complete (Karp, 1972) [1]. The search version of the problem consists in finding such an assignement.

Finding a k-coloring is equivalent to find a feasible solution to this 0-1 integer linear program:

Each vertex has a unique color:

$$\sum_{i = 1}^k x_{v, i} = 1 \  \forall v \in V$$

No adjacent vertices have the same color:

$$x_{u, i} + x_{v, i} \leq 1 \ \forall (u, v) \in E, \, i = 1, ..., k$$

Finding an k-coloring is equivalent to finding a [clique cover](../clique#clique-cover-search-and-decision-problem) of size $k$ in the graph's complement.

## Minimum coloring problem and chromatic number

The minimum problem consists in finding a minimim coloring in the graph; it is  NP-hard.

Finding a maximum independent set is equivalent to find an optimal solution to the following 0-1 integer linear program (where $w_i$ represents whether the color is used):

$$\min_{x, w} \sum_{i = 1}^{|V|}w_i$$

$$\text{s.t. } \sum_{i = 1}^{|V|} x_{v, i} = 1 \  \forall v \in V$$

$$x_{u, i} + x_{v, i} \leq w_i \ \forall (u, v) \in E, \, i = 1, ..., |V|$$


Finding a minimum coloring is equivalent to finding a [maximum clique cover](../clique#maximum-clique-cover-problem-and-clique-cover-number) in the graph's complement.

Computing the chromatic number of a graph is also NP-hard. It is equal to the [clique cover number](../clique#maximum-clique-cover-problem-and-clique-cover-number) of the graph's complement.

## Edge coloring problem and chromatic index

The edge coloring problem consists in finding a minimum edge coloring in the graph.

By Vizing's theorem (Vizing, 1964) [2], the chromatic index is almost tightly bounded by the maximum degree $\Delta(G)$ of the graph :

$$\Delta(G) \leq \chi'(G) \leq \Delta(G) + 1$$

Therefore deciding whether the graph is k-edge colorable is as hard as finding a minimum coloring and computing the chromatic index. In fact the 3 problems are NP-complete [3].

Finding a minimum edge coloring is equivalent to find a feasible solution to the following 0-1 integer linear program:

Each edge has a unique color:

$$\sum_{i = 1}^{\Delta(G)} x_{e, i} = 1 \  \forall e \in E$$

No adjacent edges have the same color:

$$\sum_{e \in \delta(u)} x_{e, i} \leq 1 \ \forall u \in V, \, i = 1, ..., \Delta(G)$$


---


[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2] Vizing, V.G. The chromatic class of a multigraph. Cybern Syst Anal 1, 32–41 (1965)

[3] Holyer, Ian (1981), "The NP-completeness of edge-coloring", SIAM Journal on Computing, 10 (4): 718–720,