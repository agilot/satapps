# Partitioning problems

Partitioning problems arises in many flavours, but they all consists in determining whether it is possible to partition a multiset of $n$ nonnegative integers $S$ according to some constraints.

## Partition problem

The partition decision problem consists in deciding whether $S$ can be partitioned in two subsets of equal sum. This problem has been proven to be NP-complete [1] The analogous search problem consists in outputing such a partition.

This problem is a special case of the [subset sum problem](#subset-sum-problem) with $B = \dfrac{\sum_{i = 1}^n S_i}{2}$ and the [k-way partitioning problem](#k-way-number-partitioning) with $k = 2$

## k-partitioning problem

The 3-partition decision problem consists in determining whether $S$ can be partitioned into triplets that all have the same sum. The 4-partition decision problem is analoguous except that we partition $S$ in 4-tuples instead. These two problems have been proven to be strongly NP-complete [2] The corresponding search problems consist in outputing such a partition.

Both problem can be generalized to the problem of dividing $S$ into k-tuples of equal sums (strongly NP-hard) [3]. If $n = 0 [k]$, finding a partition of the set is equivalent to find a feasible solution to the following 0-1 linear integer program (where $x_{ip} = 1$ means that the item $i$ belongs to the $p$-th k-tuple):

$$ \sum_{p = 1}^{\frac{n}{k}} x_{ip} = 1, \ i = 1, ..., n$$

$$ \sum_{i = 1}^n S_ix_{ip} = \dfrac{k}{n}\sum_{i = 1}^n S_i$$

$$ \sum_{i = 1}^n x_{ip} = k ,\ p = 1, ..., \dfrac{n}{k}$$

The k-partition 

## Subset sum problem

The subset sum decision problem consists in deciding whether, given a nonnegative integer $B$, there is a subset of $S$ whose elements add up to $B$. This problem has been proven to be NP-complete [1]. The corresponding search problem consists in finding such a subset.

Finding a subset that fulfills this condition is equivalent to find a feasible solution to the following 0-1 linear integer program:


$$ \sum_{i = 1}^n S_ix_{i} = B$$

## k-way number partitioning

The k-way number partitioning decision problem consists in deciding whether, given a positive integer $k$, $S$ can be divided in $k$ subsets that all have the same sum. This problem has been proven to be NP-complete [2]. The corresponding search problem consists in finding such a partition.

Finding a partition that fulfills this condition is equivalent to find a feasible solution to the following 0-1 linear integer program(where $x_{ip} = 1$ means that the item $i$ belongs to the $p$-th subset):

$$ \sum_{p = 1}^{k} x_{ip} = 1, \ i = 1, ..., n$$

$$ \sum_{i = 1}^n S_ix_{ip} = \dfrac{\sum_{i = 1}^n S_i}{k}$$


## Bin packing decision and search problem

The bin packing decision problem consists in deciding whether, given positive integers $k$ and $B$, $S$ can be partitioned into $k$ subsets such that the sum of each subset is smaller or equal than $B$. This problem has been proven to be strongly NP-complete [2]. The corresponding search problem consists in finding such a partition.

Finding a bin packing is equivalent to find a feasible solution to the following integer linear program (where $x_{ib} = 1$ means that the item $i$ belongs to the $b$-th bin):

$$ \sum_{b = 1}^{k} x_{ib} = 1, \ i = 1, ..., n$$

$$ \sum_{i = 1}^n S_i x_{ib} \leq B, \ b = 1, ..., k$$

## Bin packing problem

The bin packing problem consists in finding, given a positive integer $B$, the smallest partition of $S$ such that the sum of each subset is smaller or equal than $B$. This problem is NP-hard.

Finding a bin packing is equivalent to solve the following integer linear program (where $x_{ib} = 1$ means that the item $i$ belongs to the $b$-th bin):

$$\min_y \sum_{b=1}^{n} y_{b}$$

$$\text{s.t. } \sum_{b = 1}^{k} x_{ib} = 1, \ i = 1, ..., n$$

$$ \sum _{i = 1}^{n} S_i x_{ib} \leq B y_{b}, \ \forall b = 1, ..., n$$

## Bin packing decision and search problem

The bin packing decision problem consists in deciding whether, given positive integers $k$ and $B$, $S$ can be partitioned into $k$ subsets such that the sum of each subset is smaller or equal than $B$. This problem has been proven to be strongly NP-complete [2]. The corresponding search problem consists in finding such a partition.

Finding a bin packing is equivalent to find a feasible solution to the following integer linear program (where $x_{ib} = 1$ means that the item $i$ belongs to the $b$-th bin):

$$ \sum_{b = 1}^{k} x_{ib} = 1, \ i = 1, ..., n$$

$$ \sum_{i = 1}^n S_i x_{ib} \leq B, \ b = 1, ..., k$$

## Bin covering problem

The bin covering problem consists in finding, given a positive integer $B$, the smallest partition of $S$ such that the sum of each subset is smaller or equal than $B$. This problem is NP-hard.

Finding a bin packing is equivalent to solve the following integer linear program (where $x_{ib} = 1$ means that the item $i$ belongs to the $b$-th bin):

$$\min_y \sum_{b=1}^{n} y_{b}$$

$$\text{s.t. } \sum_{b = 1}^{k} x_{ib} = 1, \ i = 1, ..., n$$

$$ \sum _{i = 1}^{n} S_i x_{ib} \leq B y_{b}, \ \forall b = 1, ..., n$$


---

[1] Karp, Richard M., “Reducibility Among Combinatorial Problems”.
Complexity of Computer Computations, 1972: Plenum Press, 85-103.

[2]  M.R. Garey and M.R. Johnson. Computers and Intractability. Freeman, New
York, 1979.

[3] Babel, L., Kellerer, H. & Kotov, V. The k-partitioning problem. Mathematical Methods of Operations Research 47, 59–82 (1998).

[4] Martello S., Toth P., KNAPSACK PROBLEMS Algorithms and Computer Implementations, 1990.
