# Dominating set

A subset of vertices $S$ in a graph $G = (V, E)$ is an __dominating set__ if any vertex that is not in $S$ is adjacent to a vertex of $S$. A __minimum dominating set__ is a dominating set of smallest possible size. This size is called the __domination number__ of $G$ and is usually denoted by $\gamma(G)$.

An __indepedent dominating set__ is a subset of vertices that is both a dominating set and an [independent set](/problems/indset). A __minimum independent dominating set__ is an independent dominating set of smallest possible size. This size is called the __independent domination number__ of $G$ and is usually denoted by $i(G)$.

A __total dominating set__ is a dominating set that induces a total subgraph. A __minimum total dominating set__ is a total dominating set of smallest possible size. This size is called the __total domination number__ of $G$ and is usually denoted by $\gamma_t(G)$. In order for the total domination number to be defined, the graph has to be connected.

A partition of $V$ into dominating sets is called a __domatic partition__. A __maximum domatic partition__ is a domatic partition of maximum size. This size is called the __domatic number__ of the graph.



## Dominating set search and decision problem


The dominating set decision problem consists in deciding whether a graph, given a natural integer $k$, has a dominating set of size $k$. This problem has been proven to be NP-complete [1]. The dominating set search problem consists in finding such a dominating set.

Finding a dominating set of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$\sum_{v \in N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

## Minimum dominating set problem and domination number

The minimum dominating set problem consists in finding a minimum dominating set in the graph; it is  NP-hard.

Finding a minimum dominating set is equivalent to find an optimal solution to the following 0-1 integer linear program  (where w_iw 
i
​	
  represents whether the color is used):

$$\min_x \sum_{v \in V} x_v $$

$$\text{s.t.} \sum_{v \in N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

Computing the domination number of a graph is also NP-hard.


## Independent dominating set search and decision problem


The independent dominating set decision problem consists in deciding whether a graph, given a natural integer $k$, has an independent dominating set of size $k$. This problem has been proven to be NP-complete [2]. The independent dominating set search problem consists in finding such a set.

Finding an independent dominating set of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

## Minimum independent dominating set problem and independent domination number

The minimum independent dominating set problem consists in finding a minimum independent dominating set in the graph; it is  NP-hard.

Finding a minimum independent dominating set is equivalent to find an optimal solution to the following 0-1 integer linear program:

$$\min_x \sum_{v \in V} x_v $$

$$\text{s.t. } x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in N(u) \cup \{u\}} x_v \geq 1 \ \forall u \in V$$

Computing the independent domination number of a graph is also NP-hard. It also follows immediatly from the definition that:

$$\gamma(G) \leq i(G) \leq \alpha(G)$$

## Total dominating set search and decision problem


The total dominating set decision problem consists in deciding whether a connected graph, given a natural integer $k$, has a total dominating set of size $k$. This problem has been proven to be NP-complete [3]. The total dominating set search problem consists in finding such a set.

If $k > 1$, finding a total dominating set of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

$$\sum_{v \in V} x_v = k$$

$$x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in N(u)} x_v \geq 1 \ \forall u \in V$$

## Minimum total dominating set problem and total domination number

The minimum total dominating set problem consists in finding a minimum total dominating set in the graph; it is  NP-hard.

If no vertex is total to all the others (polynomially checkable and in the opposite case the solution is the vertex in question), finding a minimum total dominating set is equivalent to find an optimal solution to the following 0-1 integer linear program:

$$\min_x \sum_{v \in V} x_v $$

$$\text{s.t. } x_u + x_{v} \leq 1 \ \forall (u, v) \in E$$

$$\sum_{v \in N(u)} x_v \geq 1 \ \forall u \in V$$

Computing the total domination number of a graph is also NP-hard. It also follows immediatly from the deinition that:

$$\gamma(G) \leq \gamma_t(G)$$

## Domatic partition search and decision problem


The domatic partition decision problem consists in deciding whether a graph, given a natural integer $k$, has a domatic partition of size $k$. This problem has been proven to be NP-complete [2]. The domatic partition search problem consists in finding such a partition.

Finding a domatic partition of size $k$ is equivalent to find a feasible solution to this 0-1 integer linear program:

Each vertex belongs to one set:

$$\sum_{i = 1}^k x_{v, i} = 1 \  \forall v \in V$$

Each set is is a dominating set:

$$\sum_{v \in N(u) \cup \{u\}} x_{v, i} \geq 1 \ \forall u \in V, \, i = 1, ..., k$$

## Domatic partition problem and domatic number

The domatic partition problem consists in finding a maximum dominating partition in the graph; it is  NP-hard.

Finding a maximum dominating set is equivalent to find an optimal solution to the following 0-1 integer linear program (where $w_i$ represents whether the partition is empty or not):

$$ \max_{x, w} \sum_{i = 1}^{|V|}w_i$$

$$\text{s.t. } \sum_{i = 1}^{|V|} x_{v, i} = 1 \  \forall v \in V$$

$$\sum_{v \in N(u) \cup \{u\}} x_{v, i} \geq 1 \ \forall u \in V, \, i = 1, ..., |V|$$

$$ x_{u, i} \leq w_i \ \forall u \in V, \, i = 1, ..., |V|$$

Computing the domatic number of a graph is also NP-hard. However it has been proved that:

$$d(G) \leq \delta(G) + 1$$

where $\delta(G)$ is the minimum degree of a vertex of $G$ [4].

---


[1] Hedetniemi, S. T.; Laskar, R. C. (1990), "Bibliography on domination in graphs and some basic definitions of domination parameters", Discrete Mathematics, 86 (1–3): 257–277.

[2] M.R. Garey and M.R. Johnson. Computers and Intractability. Freeman, New
York, 1979.

[3] Michael A. Henning, Anders Yeo. Total Domination in Graphs. Springer, 2013.

[4] E.J. Cockayne and S.T. Hedetniemi, Towards a theory of domination in graphs, Networks 7 (1977)
247-261.