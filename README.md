# cnfgraphs_vibe

Playing with primal graphs via vibe coding

## Start with a CNF

I generate a CNF using CBMC, for example:

```bash
cbmc target.c --dimacs --outfile target.cnf
```

## Turn CNF into Constraint Graph

```bash
python3 cnf_to_graph.py ./target.cnf ./target.gr
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

*Warning*, will create mathplotlib widget.

```bash
python3 visualise_buckets.py target.td -o target.svg
```

### Without Bags

```bash
python3 visualise_td.py target.td -o target.svg
```
 
