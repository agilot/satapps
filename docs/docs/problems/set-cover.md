# Set Cover and Packing

Let $\mathcal{U}$ be a universe and $\mathcal{S}$ a collection of subsets of $\mathcal{U}$. A __cover__ is a subcollection $\mathcal{C} \subseteq \mathcal{S}$ such that every element of $\mathcal{U}$ appears at least once in $\mathcal{C}$. On the other hand, a __packing__ is a subcollection $\mathcal{C} \subseteq \mathcal{S}$ such that all sets in $\mathcal{C}$ are pairwise disjoint. If $\mathcal{C}$ is both a cover and a packing then it is an __exact cover__ of $\mathcal{U}$.

A __maximum packing__ is the largest packing one can find for $\mathcal{U}$ while a __minimum cover__ is the smallest cover one can find for $\mathcal{U}$.

A __hitting set__ is a subset $\mathcal{U}^* \subseteq \mathcal{U}$ such that each subset in $\mathcal{S}$ contains at least one element of $\mathcal{U}^*$. An __exact hitting set__ is a hitting set such that each subset in $\mathcal{S}$ contains exactly one element of $\mathcal{U}^*$.

A __minimum hitting set__ is the smallest hitting set one can find for $\mathcal{U}$.

## Set cover decision and search problem

The set cover decision problem consists in deciding whether, given a natural integer $k$, there exists a cover $\mathcal{C}$ of $\mathcal{U}$ such that $|\mathcal{C}| \leq k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The corresponding search problem consists in outputing such a cover.

Finding a set cover of $k$ elements is equivalent to find a feasible solution to the following 0-1 integer linear program:

$$\sum_{s \in \mathcal{S}} x_s \leq k$$

$$\sum_{s:e \in s} x_s \geq 1 \  \forall e \in \mathcal{U} $$

## Minimum set cover problem

The minimum set cover problem consists in finding a minimum set cover of $\mathcal{U}$; it is NP-hard.

The 0-1 integer linear programming formulation of the problem is the following [2]:

$$\min_x \sum_{s \in \mathcal{S}} x_s $$

$$\text{s.t. } \sum_{s:e \in s} x_s \geq 1 \  \forall e \in \mathcal{U} $$


## Set packing decision and search problem

The set packing decision problem consists in deciding whether, given a natural integer $k$, there exists a packing $\mathcal{C}$ of $\mathcal{U}$ such that $|\mathcal{C}| = k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The corresponding search problem consists in outputing such a packing.

Finding a set packing of $k$ elements is equivalent to finding a feasible solution to the following 0-1 integer linear program:

$$\sum_{s \in \mathcal{S}} x_s \geq k$$

$$\sum_{s:e \in s} x_s \leq 1 \  \forall e \in \mathcal{U} $$

Finding a solution for the problem is also equivalent to find an [independent set](../indset#independent-set-search-and-decision-problem) of size $k$ in the following graph: for each element of $\mathcal{S}$ create a vertex, and add an edge between two vertices if the intersection of their corresponding sets is non empty (Proof 1).

<details class="arithmatex"> <summary><b>Proof 1</b></summary> 
<ul>
<li> If there exists an independent set \(I\) of size \(k\) in the graph then any pair of vertices in \(I\) is not connected which implies that their respective sets are disjoints.</li>
<li> If there is no such set then for any subcollection of \(k\) elements of \(\mathcal{S}\), at least one pair of set is not disjoint.</li>
</ul> </details>

## Maximum set packing problem

The maximum set packing problem consists in finding a maximum set packing of $\mathcal{U}$; it is NP-hard.

The 0-1 integer linear programming formulation of the problem is the following [2]:

$$\max_x \sum_{s \in \mathcal{S}} x_s $$

$$\text{s.t. } \sum_{s:e \in s} x_s \leq 1 \  \forall e \in \mathcal{U} $$

Solving the problem is also equivalent to find 
a [maximum independent set](../indset#maximum-independent-set-problem-and-independence-number) in the above construction.

## Exact cover problem

The exact set cover decision problem consists in deciding whether $U$ admits an exact cover. This problem has been proven to be NP-complete (Karp, 1972) [1]. The corresponding search problem consists in outputing such a cover.

Finding an exact cover is equivalent to finding a feasible solution to the following 0-1 integer linear program:

$$\sum_{s:e \in s} x_s = 1 \  \forall e \in \mathcal{U} $$

## Hitting set decision and search problem

The hitting set decision problem consists in deciding whether, given a natural integer $k$, there exists a hitting set $\mathcal{U}^*$ such that $|\mathcal{U}| \leq k$. This problem has been proven to be NP-complete (Karp, 1972) [1]. The corresponding search problem consists in outputing such a set.

Finding a hitting set of $k$ elements is equivalent to find a feasible solution to the following 0-1 integer linear program:

$$\sum_{u \in \mathcal{U}} x_u \leq k$$

$$\sum_{u \in s} x_u \geq 1 \  \forall s \in \mathcal{S} $$

## Minimum hitting set problem

The minimum hitting set problem consists in finding a minimum hitting set of $\mathcal{U}$; it is NP-hard.

The 0-1 integer linear programming formulation of the problem is the following:

$$\min_x \sum_{u \in \mathcal{U}} x_u $$

$$\sum_{u \in s} x_u \geq 1 \  \forall s \in \mathcal{S} $$

## Exact hitting set problem

The exact hitting set decision problem consists in deciding whether $U$ admits an exact hitting set. This problem is also NP-complete (Proof 2). The corresponding search problem consists in outputing such a cover.

Finding an exact hitting set is equivalent to finding a feasible solution to the following 0-1 integer linear program:

$$\sum_{u \in s} x_u = 1 \  \forall s \in \mathcal{S} $$

<details class="arithmatex">
  <summary><b>Proof 2</b></summary>
  The exact hitting set problem is trivially in NP as we can linearly iterate over \(\mathcal{S}\) to verify a solution.

  To prove that it is NP-hard, we will build a reduction from the [exact set cover problem](#exact-cover-problem):

  Let \(\langle \mathcal{U}, \mathcal{S} \rangle\) be an instance of exact set cover. Let \[\mathcal{S}'= \{\{s: u \in s\ |\ s \in S\} \ |\  u\in \mathcal{U}\}\]

  That is, for each element in the universe build a set containing all the subsets of \(\mathcal{S}\) that contain it.
  <ul>
  <li> Define the following function on the input: \[f(\langle \mathcal{U}, \mathcal{S} \rangle) = \langle \mathcal{S}, \mathcal{S}'\rangle\] </li>

  <li> If \( \langle \mathcal{S}, \mathcal{S}'\rangle \in \textup{EXACTHITTINGSET} \), then there exists a subset  \( \mathcal{S}^* \) such that each subset in \(\mathcal{S}'\) contains exactly one element of \(\mathcal{S}^* \). This means by definition of \(\mathcal{S}'\), that for every \(u \in \mathcal{U}\) there is exactly one set  \(s \in \mathcal{S}^* \) such that \(u \in s\). This implies that \(\mathcal{S}^* \) is an exact set cover of $\mathcal{U}$ and therefore, that \( \langle \mathcal{U}, \mathcal{S}\rangle \in \textup{EXACTCOVER}\). </li>
  <li> If 
  \(\langle \mathcal{U}, \mathcal{S}\rangle \in \textup{EXACTCOVER} \), then there exists a subscollection \( \mathcal{C} \subseteq \mathcal{S} \) such that every \( u \in \mathcal{U} \) is contained in exactly one element of \(\mathcal{C}\). This means that each element of \(\mathcal{S}'\) contains exactly one element of \(\mathcal{C}\). Therefore, \(\mathcal{C}\) is an exact hitting set and \(\langle \mathcal{S}, \mathcal{S}'\rangle \in \textup{EXACTHITTINGSET}\). </li>
  </ul>
</details>

## Set Splitting

The set splitting decision problem consists in determining whether there exists a partition $(\mathcal{U}_1, \mathcal{U}_2)$ of $\mathcal{U}$ such that all subsets in $\mathcal{S}$ are neither entirely contained in $\mathcal{U}_1$ nor in  $\mathcal{U}_2$. This problem has been proven to be NP-complete since it is equivalent to hypergraph 2-coloring [3]. The corresponding search problem consists in outputing such a partition.

Finding a set splitting partition is equivalent to finding  the following 0-1 integer linear program:

$$ 0 < \sum_{u \in s} x_u < |s| \: \forall s \in \mathcal{S}$$

---

[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2] Vazirani, Vijay V. (2001), Approximation Algorithms, Springer-Verlag.

[3] Lovasz, L. (1973), "Coverings and colorings of hypergraph" Proc. 4th Southeastern Conference on Combinatorics, Graph Theory, and Computing, Utilitas Mathematica Publishing, Winnipeg, 3-12