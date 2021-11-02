# SAT-Apps (Under construction)
In complexity theory, the Cook-Levin theorem states that the Boolean
satisfiability problem, better known as SAT, is NP-complete, i.e. any
problem in NP is polynomially reducible to SAT.\
The scope of this library is thus to:
- Implement efficient modern SAT solvers
- Reduce a bunch of NP problems to SAT instances and solve them efficiently
- Reduce harder problems to SAT instances in order to solve them relatively efficiently

### Solvers at disposal
- Brute Force
- DPLL

### Currently the library tackles the following problems
- Graph coloring
- Independent set
- Clique
- Set packing
- Sudoku
- Vertex cover

### We plan to add in the future
- Graph Isomorphism
- Set cover
- Subset sum
- Presburger arithmetic
- Bounded Model Checking