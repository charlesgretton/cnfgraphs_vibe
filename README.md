# cnfgraphs_vibe

Playing with primal graphs via vibe coding 

## Start with a CNF

I generate a CNF using CBMC, for example:

```bash
cbmc target.c --dimacs --outfile target.cnf
```

## Turn CNF into Constraint Graph

```bash
python3 cnf_to_graph.py ./target.cnf ./target.gr --type primal
```

## Use HTD to Generate a Tree Decomposition

An example HTD code and repository is [here](https://github.com/mabseher/htd)

### Build

```bash
mkdir build
cd build
cmake ../
make
```
### Run

```bash
cd ./bin/
./htd_main < target.gr > target.td
```

## Verify Decomposition

```bash
python3 verify_td.py target.gr target.td
```

## Visualise Decomposition

### With Bags

*Warning*, will create matplotlib widget.

```bash
python3 visualise_bags.py target.td -o target.svg
```

### Without Bags

```bash
python3 visualise_td.py target.td -o target.svg
```

# DAG input for Dagster

The following is not yet robust to tree decompositions where nodes can be empty and vacuous. 

## DAG from a Root to the Leaves

```bash
python3 td2dag.py chain1.cnf chain1.td   2> /dev/null
```

## DAG from the Leaves to a Root

```bash
python3 td2dag.py --toroot ../chain1.cnf ../chain1.td   2> /dev/null
```

# Resources

In addition to textbooks on AI and Constraints Processing, the below exists.

## Graph Theory 6-3: Tree Decompositions and Tree Width 
 
Introduces tree decompositions and [treewidth](https://www.youtube.com/watch?v=gCZrasaG0vA), foundational concepts for analyzing graph structure and solving NP-hard problems efficiently. While not SAT-specific, it provides the theoretical basis for applications in constraint satisfaction problems like SAT.

## Induced Subgraphs and Tree Decompositions

A [talk by Maria Chudnovsky](https://youtu.be/cF7fJT7iFnM?si=tyiq0foWp1pt1CKb&t=717) (Princeton University) at IWOCA 2021, exploring structural graph theory techniques applicable to SAT instances . It emphasizes how decompositions simplify solving combinatorial problems by leveraging sparsity.

## Daniel Lokshtanov: Tree Decompositions and Graph Algorithms

Discusses algorithmic [applications of tree decompositions](https://www.youtube.com/watch?v=AW3MVauVrik), including dynamic programming on graphs-a strategy often used in SAT solvers for structured instances.

## Background on Junction Tree Algorithm

Tree decompositions (also called [junction trees](https://youtu.be/d8tKC5vxVv8?si=HhN_iJO72-0SfaHW) or clique trees) for graphical models. How to construct a tree decomposition from a graph (which, in the context of SAT, is often the primal graph).

## Connection to SAT Primal Graphs

You can access the paper directly [here](https://pageperso.lis-lab.fr/cyril.terrioux/en/publis/ictai2009a.pdf)
