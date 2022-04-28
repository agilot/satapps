# Vertex cover

A subset of vertices $S$ in a graph $G = (V, E)$ is a __vertex cover__ if every edge of the graph has an endpoint in $S$.

A __minimum vertex cover__ is a vertex cover of smallest possible size. This size is called the __vertex cover number__ of $G$ and is usually denoted by $\tau(G)$.



## Vertex cover search decision problem


The vertex cover decision problem consists in deciding whether a graph, given a natural integer $k$, has a vertex cover of size $k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The vertex cover search problem consists in finding such a set.

Finding a vertex cover of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$x_u + x_{v} \geq 1 \ \forall (u, v) \in E$$

Finding an vertex cover of size $k$ is equivalent to finding an [independent set](/problems/indset#independent-set-decision-problem) of size $|V| - k$ since its complement is going to be a vertex cover.

## Minimum vertex cover problem and vertex cover number

The minimum vertex cover problem consists in finding a minimum vertex cover in the graph; it is  NP-hard.

Finding a minimum vertex cover is equivalent to find an optimal solution to the following 0-1 integer linear program:

$$\min_x \sum_{v \in V} x_v $$

$$\text{s.t.} x_u + x_{v} \geq 1 \ \forall (u, v) \in E$$

Finding a minimum vertex cover is  equivalent to finding a [maximum independent set](/problems/indset#maximum-independent-set-problem) and take its complement.

Computing the vertex cover number of a graph is also NP-hard and is equal to the number of vertices minus the [independence number](/problems/indset#independence-number) of the graph (Gallai 1959) [2]

---


[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2] T. Gallai, Über extreme Punkt-und Kantenmengen. Ann. Univ. Sci. Budapest, Eötvös Sect.
Math. 2 (1959) 133-138