# cnfgraphs_vibe

Playing with primal graphs via vibe coding 

## Start with a CNF

I generate a CNF using CBMC, for example:

```bash
cbmc ./examples/C/ex1.c --dimacs --outfile x.cnf
```

## Turn CNF into Constraint Graph

```bash
python3 cnf_to_graph.py ./x.cnf ./x.gr  --type primal
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
htd_main --triangulation-minimization  --preprocessing full --opt width --strategy min-degree < x.gr > x.td
```

## Verify Decomposition

```bash
python3 verify_td.py x.gr x.td
```

## Visualise Decomposition

### With Bags

*Warning*, will create matplotlib widget.

```bash
python3 visualise_bags.py x.td -o x.svg
```

### Without Bags

```bash
python3 visualise_td.py x.td -o x.svg
```

## Get One Subproblem

The tree decomposition may be a forest, with each subtree to be solved individually. Here, I get the biggest subtree. 

```bash
python3 biggest_component.py x.td x.1c.td
```

## Remove Empty Bags

A tree decomposition may produce bags that are empty. Here, we have a script to remove those. 

```bash
python3 remove_empty_bags.py x.cnf x.1c.td x.1c.nempt.td
```

# DAG input for Dagster

## Auxiliary Clause

A bag does not necessarily have to have constraints associated with it, and in this case we need a vacuous additional clause for Dagster to associate with such bags. 


```bash
python3 add_one_var_to_cnf.py x.cnf x.plus1.cnf
```

## DAG from a Root to the Leaves

```bash
python3 td2dag.py x.cnf x.1c.nempt.td   2> /dev/null > x.dag
```

## DAG from a Leaves to the Root

```bash
python3 td2dag.py -toroot x.cnf x.1c.nempt.td   2> /dev/null > x.dag
```

## Run Dagster

On a small host, you could test with the following invocation.

```bash
mpirun --oversubscribe -n 100 ./dagster -m 0 -b 0 -e 0  x.dag x.plus1.cnf
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
