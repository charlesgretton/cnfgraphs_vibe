## Author -- Gemini 2.5 Pro Preview 05-06

import argparse
import os

def parse_cnf_dimacs(cnf_filepath):
    """
    Parses a CNF file in DIMACS format.

    Args:
        cnf_filepath (str): Path to the CNF file.

    Returns:
        tuple: (num_variables, num_clauses_expected, list_of_clauses)
               list_of_clauses contains lists of integers (literals).
               Returns (None, None, None) on parsing error.
    """
    clauses = []
    num_variables = 0
    num_clauses_expected = 0
    parsed_problem_line = False

    try:
        with open(cnf_filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('c'):
                    continue
                parts = line.split()
                if line.startswith('p cnf'):
                    if parsed_problem_line:
                        print(f"Error: Multiple 'p cnf' lines found.")
                        return None, None, None
                    if len(parts) != 4:
                        print(f"Error: Malformed 'p cnf' line: {line}")
                        return None, None, None
                    try:
                        num_variables = int(parts[2])
                        num_clauses_expected = int(parts[3])
                        parsed_problem_line = True
                    except ValueError:
                        print(f"Error: Non-integer values in 'p cnf' line: {line}")
                        return None, None, None
                elif parsed_problem_line:
                    try:
                        literals = [int(p) for p in parts]
                        if not literals or literals[-1] != 0:
                            print(f"Error: Clause line does not end with 0: {line}")
                            return None, None, None
                        clauses.append(literals[:-1]) # Remove trailing 0
                    except ValueError:
                        print(f"Error: Non-integer literal in clause: {line}")
                        return None, None, None
                else:
                    print(f"Error: Encountered data line before 'p cnf' line: {line}")
                    return None, None, None
        
        if not parsed_problem_line and (num_variables > 0 or num_clauses_expected > 0 or clauses):
            print("Error: No 'p cnf' line found, but data seems present.")
            return None, None, None
        if not parsed_problem_line and not clauses: # Empty file or only comments
             print("Warning: CNF file appears empty or contains only comments.")
             return 0, 0, []


        if len(clauses) != num_clauses_expected:
            print(f"Warning: Expected {num_clauses_expected} clauses, but found {len(clauses)}.")
            # It's a warning, proceed with found clauses

        return num_variables, len(clauses), clauses

    except FileNotFoundError:
        print(f"Error: CNF file not found: {cnf_filepath}")
        return None, None, None
    except Exception as e:
        print(f"An unexpected error occurred during CNF parsing: {e}")
        return None, None, None

def generate_primal_graph(num_variables, clauses):
    """
    Generates the primal graph (variable interaction graph).

    Args:
        num_variables (int): Total number of variables.
        clauses (list of list of int): List of clauses.

    Returns:
        tuple: (graph_num_vertices, list_of_edges, graph_num_edges)
               list_of_edges contains tuples (u, v).
    """
    if num_variables == 0:
        return 0, [], 0
        
    graph_num_vertices = num_variables
    edges = set() # Use a set to automatically handle duplicates and ordering

    for clause in clauses:
        # Get unique variables involved in the clause (absolute values)
        variables_in_clause = sorted(list(set(abs(lit) for lit in clause if abs(lit) <= num_variables)))
        
        # Add edges between all pairs of unique variables in this clause
        for i in range(len(variables_in_clause)):
            for j in range(i + 1, len(variables_in_clause)):
                u, v = variables_in_clause[i], variables_in_clause[j]
                # Store in a canonical way (smaller, larger) to avoid (v,u) if (u,v) exists
                edges.add(tuple(sorted((u, v))))
    
    sorted_edges = sorted(list(edges)) # For consistent output order
    return graph_num_vertices, sorted_edges, len(sorted_edges)

def generate_incidence_graph(num_variables, clauses):
    """
    Generates the incidence graph (bipartite variable-clause graph).

    Args:
        num_variables (int): Total number of variables.
        clauses (list of list of int): List of clauses.

    Returns:
        tuple: (graph_num_vertices, list_of_edges, graph_num_edges)
               list_of_edges contains tuples (u, v).
    """
    num_actual_clauses = len(clauses)
    if num_variables == 0 and num_actual_clauses == 0:
        return 0, [], 0

    # Vertices 1 to num_variables are for variables
    # Vertices num_variables + 1 to num_variables + num_actual_clauses are for clauses
    graph_num_vertices = num_variables + num_actual_clauses
    edges = []

    for clause_idx, clause in enumerate(clauses):
        clause_node_id = num_variables + clause_idx + 1 # 1-indexed clause nodes
        for literal in clause:
            variable_node_id = abs(literal)
            if 1 <= variable_node_id <= num_variables: # Ensure variable is valid
                 # Edges are (variable_node, clause_node)
                edges.append(tuple(sorted((variable_node_id, clause_node_id)))) # canonical for consistency
            # else:
            #     print(f"Warning: Literal {literal} in clause {clause_idx+1} refers to variable {abs(literal)} "
            #           f"which is out of range [1, {num_variables}]. Skipping this literal for edge generation.")


    # Remove duplicate edges that might arise if a variable appears multiple times in a clause (e.g. (x or x))
    # or if multiple identical clauses exist (though DIMACS usually doesn't have this).
    # For incidence graph, this is less likely to be intended as "multiple edges"
    # but the problem spec allows it. For simplicity here, we make them unique.
    unique_edges = sorted(list(set(edges)))
    return graph_num_vertices, unique_edges, len(unique_edges)

def write_gr_graph(gr_filepath, num_vertices, edges, graph_type="unknown"):
    """
    Writes the graph to a .gr file in the specified DIMACS-like format.

    Args:
        gr_filepath (str): Path to the output .gr file.
        num_vertices (int): Number of vertices in the graph.
        edges (list of tuple): List of edges (u, v).
        graph_type (str): Description of the graph type for comments.
    """
    num_edges = len(edges)
    try:
        with open(gr_filepath, 'w') as f:
            f.write(f"c This file describes a {graph_type} graph derived from a CNF formula.\n")
            f.write(f"c Original CNF problem was converted to this graph.\n")
            f.write(f"p tw {num_vertices} {num_edges}\n")
            for u, v in edges:
                f.write(f"{u} {v}\n")
        print(f"Successfully wrote {graph_type} graph to: {gr_filepath}")
        print(f"Graph details: {num_vertices} vertices, {num_edges} edges.")
    except IOError:
        print(f"Error: Could not write to .gr file: {gr_filepath}")

def main():
    parser = argparse.ArgumentParser(
        description="Translate a CNF file (DIMACS) to a graph file (.gr DIMACS-like).",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument("cnf_file", help="Path to the input CNF DIMACS file.")
    parser.add_argument("gr_file", help="Path to the output .gr graph file.")
    parser.add_argument(
        "--type",
        choices=["primal", "incidence"],
        default="primal",
        help=(
            "Type of graph to generate:\n"
            "  primal    - Variable interaction graph. Vertices are variables, \n"
            "              edges connect variables co-occurring in a clause.\n"
            "  incidence - Bipartite variable-clause graph. Vertices are variables\n"
            "              and clauses, edges connect variables to clauses they appear in.\n"
            "(default: primal)"
        )
    )

    args = parser.parse_args()

    if not os.path.exists(args.cnf_file):
        print(f"Error: Input CNF file not found: {args.cnf_file}")
        return

    print(f"Parsing CNF file: {args.cnf_file}...")
    num_vars, num_cls, cls_list = parse_cnf_dimacs(args.cnf_file)

    if num_vars is None: # Error during parsing
        return

    if num_vars == 0 and not cls_list:
        print("CNF file is effectively empty. Generating an empty graph.")
        write_gr_graph(args.gr_file, 0, [], f"empty ({args.type})")
        return
    
    print(f"CNF parsed: {num_vars} variables, {num_cls} clauses found.")

    graph_v = 0
    graph_e_list = []
    # graph_e_count = 0 # The length of graph_e_list will be the count

    if args.type == "primal":
        print("Generating primal graph...")
        graph_v, graph_e_list, _ = generate_primal_graph(num_vars, cls_list)
    elif args.type == "incidence":
        print("Generating incidence graph...")
        graph_v, graph_e_list, _ = generate_incidence_graph(num_vars, cls_list)
    else:
        # Should not happen due to argparse choices
        print(f"Error: Unknown graph type '{args.type}'")
        return

    write_gr_graph(args.gr_file, graph_v, graph_e_list, args.type)

if __name__ == "__main__":
    main()
