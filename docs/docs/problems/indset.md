# Independent set

A subset of vertices $S$ in a graph $G = (V, E)$ is an __independent set__ if for every pair of vertices of $S$, there is no edge connecting the two.

A __maximum independent set__ is an independent set of largest possible size. This size is called the __independence number__ of $G$ and is usually denoted by $\alpha(G)$.

An __indepedent dominating set__ is a subset of vertices that is both an independent set and a [dominating set](../domset).

A __minimum independent dominating set__ is an independent dominating set of smallest possible size. This size is called the __independent domination number__ of $G$ and is usually denoted by $i(G)$.

A partition of $V$ into independent subsets is called a [__coloring__](../coloring).



## Independent set search and decision problem


The independent set decision problem consists in deciding whether a graph, given a natural integer $k$, has an independent set of size $k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The independent search problem consists in finding such a set.

Finding an independent set of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

Finding an independent set of size $k$ is equivalent to finding a [clique](../clique#clique-search-and-decision-problem) of size $k$ in the graph's complement. It is also equivalent to finding a [vertex cover](../vertex_cover#vertex-cover-search-and-decision-problem) of size $|V| - k$ since its complement is going to be an independent set.

## Maximum independent set problem and independence number

The maximum independent set problem consists in finding a maximum independent set in the graph; it is  NP-hard.

Finding a maximum independent set is equivalent to find an optimal solution to the following 0-1 integer linear program:

$$\max_x \sum_{v \in V} x_v $$

$$\text{s.t.} x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

Finding a maximum independent set is equivalent to finding a [maximum clique](../clique#maximum-clique-problem-and-clique-number) in the graph's complement. It is also equivalent to finding a [minimum vertex cover](../vertex_cover#minimum-vertex-cover-problem-and-vertex-cover-number) and take its complement.

Computing the independence number of a graph is also NP-hard. It is equal to the number of vertices minus the [vertex cover number](../vertex_cover#minimum-vertex-cover-problem-and-vertex-cover-number) of the graph (Gallai 1959) [2] and to the [clique number](../clique#maximum-clique-problem-and-clique-number) of the graph's complement.



## Independent dominating set search and decision problem


The independent dominating set decision problem consists in deciding whether a graph, given a natural integer $k$, has an independent dominating set of size $k$. This problem has been proven to be NP-complete [3]. The independent dominating set search problem consists in finding such a set.

Finding an independent dominating set of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in \N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

## Minimum independent dominating set problem and independent domination number

The minimum independent dominating set problem consists in finding a minimum independent dominating set in the graph; it is  NP-hard.

Finding a minimum independent dominating set is equivalent to find an optimal solution to the following 0-1 integer linear program:

$$\min_x \sum_{v \in V} x_v $$

$$\text{s.t. } x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in \N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

Computing the independent domination number of a graph is also NP-hard. It also follows immediatly from the definition that:

$$\gamma(G) \leq i(G) \leq \alpha(G)$$

---


[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2] T. Gallai, Über extreme Punkt-und Kantenmengen. Ann. Univ. Sci. Budapest, Eötvös Sect.
Math. 2 (1959) 133-138

[3] M.R. Garey and M.R. Johnson. Computers and Intractability. Freeman, New
York, 1979.