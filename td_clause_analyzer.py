import argparse
import os
from collections import defaultdict
import networkx as nx

# --- CNF Parser ---
def parse_cnf_dimacs(cnf_filepath):
    """
    Parses a CNF file in DIMACS format.
    Returns:
        tuple: (num_variables, list_of_clauses)
               list_of_clauses contains lists of integers (literals).
               Clause indices will be 0-based.
               Returns (None, None) on parsing error.
    """
    clauses = []
    num_variables = 0
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
                        print(f"Error: Multiple 'p cnf' lines found in CNF.")
                        return None, None
                    try:
                        num_variables = int(parts[2])
                        # num_clauses_expected = int(parts[3]) # Not strictly needed here
                        parsed_problem_line = True
                    except (ValueError, IndexError):
                        print(f"Error: Malformed 'p cnf' line: {line}")
                        return None, None
                elif parsed_problem_line:
                    try:
                        literals = [int(p) for p in parts]
                        if not literals or literals[-1] != 0:
                            print(f"Error: Clause line does not end with 0: {line}")
                            return None, None
                        clauses.append(literals[:-1]) # Remove trailing 0
                    except ValueError:
                        print(f"Error: Non-integer literal in clause: {line}")
                        return None, None
                else:
                    print(f"Error: Encountered clause line before 'p cnf' line: {line}")
                    return None, None
        
        if not parsed_problem_line and clauses:
            print("Error: No 'p cnf' line found in CNF, but clauses seem present.")
            return None, None
        if not parsed_problem_line and not clauses: # Empty file or only comments
             print("Warning: CNF file appears empty or contains only comments.")
             return 0, []
        return num_variables, clauses
    except FileNotFoundError:
        print(f"Error: CNF file not found: {cnf_filepath}")
        return None, None
    except Exception as e:
        print(f"An unexpected error occurred during CNF parsing: {e}")
        return None, None

# --- Tree Decomposition Parser ---
def parse_td_file(td_filepath):
    """
    Parses a tree decomposition file in .td DIMACS-like format.
    Returns:
        tuple: (dict_of_bags, list_of_td_edges) or (None, None) on error.
        dict_of_bags: {bag_id_int: set_of_variable_ids_int}
        list_of_td_edges: list of tuples (bag_id1_int, bag_id2_int)
    """
    bags = {} 
    td_edges = []
    parsed_solution_line = False

    try:
        with open(td_filepath, 'r') as f:
            for line_num, line_content in enumerate(f, 1):
                line = line_content.strip()
                if not line or line.startswith('c'):
                    continue
                
                parts = line.split()
                if not parts: continue

                if line.startswith('s td'):
                    parsed_solution_line = True
                    # We don't strictly need the header values for this script's logic
                elif line.startswith('b'): 
                    if len(parts) < 2: continue # Malformed
                    try:
                        bag_id = int(parts[1])
                        vertex_parts = parts[2:]
                        if vertex_parts and vertex_parts[-1] == '0':
                            vertex_parts = vertex_parts[:-1]
                        bag_variables = {int(v) for v in vertex_parts}
                        bags[bag_id] = bag_variables
                    except ValueError:
                        print(f"Warning: Non-integer in TD bag line {line_num}: {line_content}. Skipping.")
                        continue
                elif parsed_solution_line or bags: # Assume edge if not 's' or 'b' and after s/first b
                    edge_node_parts = parts
                    if edge_node_parts and edge_node_parts[-1] == '0':
                        edge_node_parts = edge_node_parts[:-1]
                    if len(edge_node_parts) != 2: continue # Malformed
                    try:
                        u_bag, v_bag = int(edge_node_parts[0]), int(edge_node_parts[1])
                        td_edges.append(tuple(sorted((u_bag, v_bag))))
                    except ValueError:
                        print(f"Warning: Non-integer in TD edge line {line_num}: {line_content}. Skipping.")
                        continue
        
        td_edges = sorted(list(set(td_edges))) 
        if not bags and not td_edges:
            print(f"Warning: No bags or TD edges found in {td_filepath}.")
            return {}, [] # Return empty structures
        
        # Ensure all nodes mentioned in edges are in bags (even if empty)
        # This is important if a TD file only lists edges and assumes nodes exist.
        all_edge_nodes = set()
        for u,v in td_edges:
            all_edge_nodes.add(u)
            all_edge_nodes.add(v)
        for node_id in all_edge_nodes:
            if node_id not in bags:
                print(f"Info: TD node {node_id} found in an edge but not in a 'b' line. Adding as empty bag.")
                bags[node_id] = set()
        if not bags and all_edge_nodes: # Only edges, no 'b' lines
             print("Warning: No 'b' lines in TD file, bags inferred from edges only.")

        return bags, td_edges
    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None
    except Exception as e:
        print(f"An unexpected error occurred during TD parsing: {e}")
        return None, None

# --- Main Logic ---
def analyze_td_clauses(cnf_filepath, td_filepath, root_bag_id_param=None):
    # 1. Parse CNF
    print(f"Parsing CNF file: {cnf_filepath}...")
    num_vars, cnf_clauses = parse_cnf_dimacs(cnf_filepath)
    if cnf_clauses is None:
        return
    if not cnf_clauses:
        print("No clauses found in CNF file.")
        # Proceed if TD exists, but clause association part will be empty.

    # Preprocess clauses to get sets of variables involved (absolute values)
    # Store with original 0-based index
    clauses_with_vars = []
    for i, clause_literals in enumerate(cnf_clauses):
        vars_in_clause = {abs(lit) for lit in clause_literals if lit != 0}
        clauses_with_vars.append({'id': i, 'vars': vars_in_clause, 'literals': clause_literals})
    print(f"Parsed {len(cnf_clauses)} clauses from CNF.")

    # 2. Parse Tree Decomposition
    print(f"\nParsing Tree Decomposition file: {td_filepath}...")
    td_bags, td_edges = parse_td_file(td_filepath)
    if td_bags is None:
        return
    if not td_bags and not td_edges:
        print("No bags or edges found in TD file. Cannot proceed.")
        return
    if not td_bags and td_edges: # only edges, bags were inferred as empty
        print("Warning: TD file contained only edges. Bags were inferred as empty.")

    print(f"Parsed {len(td_bags)} bags and {len(td_edges)} TD edges.")

    # 3. Associate clauses with bags
    print("\n--- Clauses per TD Vertex ---")
    bag_to_clause_indices = defaultdict(list)
    # Sort bag IDs for consistent output order
    sorted_bag_ids = sorted(td_bags.keys())

    for bag_id in sorted_bag_ids:
        bag_vars = td_bags.get(bag_id, set()) # Use .get for safety if bag_id from edge not in bags dict
        for clause_info in clauses_with_vars:
            # A clause is comprised only of variables from the bag if all its variables are in the bag
            if clause_info['vars'].issubset(bag_vars):
                bag_to_clause_indices[bag_id].append(clause_info['id'])
        
        clause_indices_str = ", ".join(map(str, sorted(bag_to_clause_indices[bag_id])))
        print(f"{bag_id} : {clause_indices_str}")


    # 4. Build TD graph and find paths from leaves to root/trunk
    if not td_bags: # Need bags (nodes) to build a graph
        print("\nNo bags defined in TD, skipping path printing.")
        return
        
    td_graph = nx.Graph()
    if td_bags: # Add nodes only if bags were defined
        td_graph.add_nodes_from(td_bags.keys())
    td_graph.add_edges_from(td_edges)

    if not td_graph.nodes():
        print("\nTD graph has no nodes, skipping path printing.")
        return
    
    if not nx.is_connected(td_graph) and len(td_graph.nodes()) > 1:
        print("\nWarning: The tree decomposition graph is not connected. Path finding might be incomplete.")
        # Could try to find paths within each connected component to a local "root" if desired.

    # Determine the root/trunk
    root_node = None
    if root_bag_id_param is not None:
        if root_bag_id_param in td_graph:
            root_node = root_bag_id_param
            print(f"\nUsing specified root/trunk: {root_node}")
        else:
            print(f"Warning: Specified root ID {root_bag_id_param} not in TD. Choosing default root.")
            root_bag_id_param = None # Fallback to default

    if root_node is None:
        if td_graph.nodes():
            # Heuristic: pick node with smallest ID, or one with high degree, or just min ID.
            # Smallest ID is simple and deterministic.
            root_node = min(td_graph.nodes())
            print(f"\nUsing default root/trunk (smallest bag ID): {root_node}")
        else:
            print("\nCannot determine root, no nodes in TD graph.")
            return

    # Find leaves
    leaves = [node for node in td_graph.nodes() if td_graph.degree(node) == 1]
    if not leaves and len(td_graph.nodes()) == 1: # Single node graph
        leaves = [root_node] # The root is also a leaf
    elif not leaves and len(td_graph.nodes()) > 1: # No leaves in a multi-node graph (e.g. a cycle - not a tree)
        print("Warning: No leaves found in the TD graph (it might not be a tree). Path printing might be unusual.")
        # As a fallback, could pick all nodes except root as potential "leaves" for path demo
        # For now, let's proceed if leaves were identified.

    print("\n--- Paths from Leaves to Trunk ---")
    if not leaves:
        print("No leaves identified to trace paths from.")
    
    path_count = 0
    for leaf in leaves:
        if leaf == root_node and len(td_graph.nodes()) > 1: # Don't trace path from root to itself unless it's the only node
            continue
        try:
            # In a tree, there's a unique simple path
            path = nx.shortest_path(td_graph, source=leaf, target=root_node)
            path_count += 1
            print(f"Path from leaf {leaf} to trunk {root_node}:")
            if len(path) == 1: # Path is just the leaf itself (it's the root)
                 print(f"  {path[0]} (is trunk)")
            else:
                for i in range(len(path) - 1):
                    print(f"  {path[i]}->{path[i+1]}")
        except nx.NetworkXNoPath:
            print(f"  No path found from leaf {leaf} to trunk {root_node} (TD might be disconnected).")
        except nx.NodeNotFound:
            print(f"  Error: Node {leaf} or {root_node} not found in graph during path search.")
    
    if path_count == 0 and leaves and (len(td_graph.nodes()) > 1 or (len(td_graph.nodes())==1 and leaves[0] != root_node)):
        print("No paths were printed (e.g. all leaves were the root, or errors occurred).")
    elif path_count == 0 and not leaves and len(td_graph.nodes()) > 0:
        print("No leaves found, so no paths to print.")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze a Tree Decomposition against a CNF file. "
                    "Associates CNF clauses with TD bags and prints paths from leaves to a root."
    )
    parser.add_argument("cnf_file", help="Path to the input CNF DIMACS file.")
    parser.add_argument("td_file", help="Path to the input Tree Decomposition (.td) file.")
    parser.add_argument(
        "--root", type=int, default=None,
        help="Optional: Specify the ID of the TD bag to be considered the 'trunk' or root. "
             "If not provided, the bag with the smallest ID will be chosen."
    )
    args = parser.parse_args()

    if not os.path.exists(args.cnf_file):
        print(f"Error: Input CNF file not found: {args.cnf_file}")
        return
    if not os.path.exists(args.td_file):
        print(f"Error: Input .td file not found: {args.td_file}")
        return

    analyze_td_clauses(args.cnf_file, args.td_file, args.root)

if __name__ == "__main__":
    main()