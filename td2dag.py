## Author -- Gemini 2.5 Pro Preview 05-06
## With extensions, corrections and logging changes by Charles Gretton - May 15, 2025 

import argparse
import os
from collections import defaultdict
import networkx as nx
import logging

logging.basicConfig(level=logging.DEBUG, format='%(levelname)s: %(message)s')

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
                        logging.error(f"Error: Multiple 'p cnf' lines found in CNF.")
                        return None, None
                    try:
                        num_variables = int(parts[2])
                        # num_clauses_expected = int(parts[3]) # Not strictly needed here
                        parsed_problem_line = True
                    except (ValueError, IndexError):
                        logging.error(f"Error: Malformed 'p cnf' line: {line}")
                        return None, None
                elif parsed_problem_line:
                    try:
                        literals = [int(p) for p in parts]
                        if not literals or literals[-1] != 0:
                            logging.error(f"Error: Clause line does not end with 0: {line}")
                            return None, None
                        clauses.append(literals[:-1]) # Remove trailing 0
                    except ValueError:
                        logging.error(f"Error: Non-integer literal in clause: {line}")
                        return None, None
                else:
                    logging.error(f"Error: Encountered clause line before 'p cnf' line: {line}")
                    return None, None
        
        if not parsed_problem_line and clauses:
            logging.error("Error: No 'p cnf' line found in CNF, but clauses seem present.")
            return None, None
        if not parsed_problem_line and not clauses: # Empty file or only comments
             logging.warning("Warning: CNF file appears empty or contains only comments.")
             return 0, []
        return num_variables, clauses
    except FileNotFoundError:
        logging.error(f"Error: CNF file not found: {cnf_filepath}")
        return None, None
    except Exception as e:
        logging.info(f"An unexpected error occurred during CNF parsing: {e}")
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
                        logging.warning(f"Warning: Non-integer in TD bag line {line_num}: {line_content}. Skipping.")
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
                        logging.warning(f"Warning: Non-integer in TD edge line {line_num}: {line_content}. Skipping.")
                        continue
        
        td_edges = sorted(list(set(td_edges))) 
        if not bags and not td_edges:
            logging.warning(f"Warning: No bags or TD edges found in {td_filepath}.")
            return {}, [] # Return empty structures
        
        # Ensure all nodes mentioned in edges are in bags (even if empty)
        # This is important if a TD file only lists edges and assumes nodes exist.
        all_edge_nodes = set()
        for u,v in td_edges:
            all_edge_nodes.add(u)
            all_edge_nodes.add(v)
        for node_id in all_edge_nodes:
            if node_id not in bags:
                logging.info(f"Info: TD node {node_id} found in an edge but not in a 'b' line. Adding as empty bag.")
                bags[node_id] = set()
        if not bags and all_edge_nodes: # Only edges, no 'b' lines
             logging.warning("Warning: No 'b' lines in TD file, bags inferred from edges only.")

        return bags, td_edges
    except FileNotFoundError:
        logging.error(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None
    except Exception as e:
        logging.error(f"An unexpected error occurred during TD parsing: {e}")
        return None, None


edges__from_leaf_to_root = {}
edges__from_root_to_leafs = {}
bag_to_clause_indices = defaultdict(list) # I depart from Habet et al., and allow a clause to appear in multiple tree nodes (i.e., I do not exclude 'parent' clauses)

clauses = []
num_vars = 0
td_bags = {} 
td_edges = []
td_leaves = None
root_node = None
td_graph = nx.Graph()
clauses_with_vars = []

def print_edge_map_with_source_clause_variables(input_edge_map, map_name="Edge Map"):
    """
    Prints each element of an input_edge_map (source_bag -> destination_bag)
    along with a comma-separated list of variables from clauses associated
    with the source_bag.

    Args:
        input_edge_map (dict): A dictionary where keys are source bag IDs
                               and values are destination bag IDs.
                               Example: {1: 2, 2: 4}
        map_name (str): A descriptive name for the map being printed.
    """
    global bag_to_clause_indices # To get clauses for source_bag
    global clauses_with_vars     # To get variables from those clauses

    logging.info(f"\n--- {map_name} with Source Clause Variables ---")

    if not input_edge_map:
        logging.warning(f"The provided '{map_name}' is empty. Nothing to print.")
        return

    # Iterate through the map, sorting by source bag ID for consistent output
    for source_bag_id in sorted(input_edge_map.keys()):
        destination_bag_id = input_edge_map[source_bag_id]

        # --- Get variables from clauses associated with the source_bag_id ---
        variables_in_source_clauses = set()
        
        # Check if the source_bag_id has any clauses associated with it
        if source_bag_id in bag_to_clause_indices:
            for clause_id in bag_to_clause_indices[source_bag_id]:
                # clauses_with_vars is a list of dicts.
                # The 'id' in each dict corresponds to its index in this list.
                if 0 <= clause_id < len(clauses_with_vars):
                    variables_in_source_clauses.update(clauses_with_vars[clause_id]['vars'])
                else:
                    # This indicates an inconsistency if it happens
                    logging.warning(f"Warning: Clause ID {clause_id} (from bag {source_bag_id}) is out of range for 'clauses_with_vars'.")
        
        # Format the set of variables into a sorted, comma-separated string
        vars_str = ",".join(map(str, sorted(list(variables_in_source_clauses))))
        
        print(f"{source_bag_id}->{destination_bag_id}:{vars_str}")


def print_clauses_for_each_bag():
    """
    Iterates through all known TD bags and prints the clause indices
    associated with each bag from the global `bag_to_clause_indices` dictionary.
    """
    global td_bags # Accessing global td_bags to get all bag IDs
    global bag_to_clause_indices # Accessing global bag_to_clause_indices for reading

    if not td_bags:
        logging.info("No TD bags defined (td_bags dictionary is empty). Cannot print clauses per bag.")
        return

    # We should iterate over the keys of td_bags to ensure we consider all defined bags,
    # even if some might not have clauses associated with them (defaultdict would handle those).
    # Sorting bag IDs for consistent output order.
    sorted_bag_ids = sorted(td_bags.keys())

    for bag_id in sorted_bag_ids:
        # Get the list of clause indices for the current bag_id.
        # If bag_id is not in bag_to_clause_indices (e.g., a bag with no covering clauses),
        # defaultdict(list) will return an empty list.
        clause_indices_for_this_bag = bag_to_clause_indices[bag_id]
        
        # Format the list of clause indices into a comma-separated string.
        # The indices should already be sorted if you sorted them when populating bag_to_clause_indices.
        # If not, you could sort here: sorted(clause_indices_for_this_bag)
        clause_indices_str = ",".join(map(str, clause_indices_for_this_bag))
        
        print(f"{bag_id}:{clause_indices_str}")

    if not sorted_bag_ids: # Second check if td_bags became empty after sorting (shouldn't happen)
        logging.info("No bag IDs found to process.")


def compute__root_paths_to_leaves():
    global td_bags, td_edges, root_node, td_graph, td_leaves, edges__from_root_to_leafs
    
    # Ensure necessary globals are initialized
    if td_leaves is None or root_node is None or not td_graph.nodes():
        logging.error("Error: TD graph, leaves, or root_node not initialized for compute__root_paths_to_leaves.")
        return

    # Clear the dictionary before populating, in case this function is called multiple times
    edges__from_root_to_leafs.clear()
    
    path_count = 0
    logging.info(f"\nComputing paths from root {root_node} to leaves: {td_leaves}")

    for leaf in td_leaves:
        if leaf == root_node and len(td_graph.nodes()) == 1: # Path from root to itself if it's the only node
            # No edges to add in this case for edges__from_root_to_leafs
            logging.info(f"  Path from root {root_node} to leaf {leaf} (is the same node).")
            path_count +=1
            continue
        if leaf == root_node and len(td_graph.nodes()) > 1: # Root cannot be a leaf if there are other nodes
            continue

        try:
            # Find the path from the root to the current leaf
            path = nx.shortest_path(td_graph, source=root_node, target=leaf)
            path_count += 1
            # print(f"  Path from root {root_node} to leaf {leaf}: {path}") # For debugging

            if len(path) > 1: # Path has at least one edge
                for i in range(len(path) - 1):
                    # path[i] is closer to the root (source)
                    # path[i+1] is further from the root, towards the leaf (destination)
                    current_source = path[i]
                    current_destination = path[i+1]
                    
                    # If you want to store multiple children for a source:
                    # if current_source not in edges__from_root_to_leafs:
                    #     edges__from_root_to_leafs[current_source] = []
                    # if current_destination not in edges__from_root_to_leafs[current_source]:
                    #     edges__from_root_to_leafs[current_source].append(current_destination)
                    
                    # If sticking to source:destination (overwrites if source has multiple children on different paths)
                    edges__from_root_to_leafs[current_source] = current_destination
                    
        except nx.NetworkXNoPath:
            # This should ideally not happen if leaves are reachable from root in a tree
            logging.info(f"  No path found from root {root_node} to leaf {leaf} (TD might be disconnected or root not an ancestor).")
        except nx.NodeNotFound:
            logging.error(f"  Error: Node {root_node} or {leaf} not found in graph during path search.")
            
    # print(f"Processed {path_count} paths from root. Populated edges__from_root_to_leafs.")


    
def compute__leaf_paths_to_root():
    global td_bags
    global td_edges
    global root_node
    global td_graph
    global td_leaves
    global edges__from_leaf_to_root
    
    path_count = 0
    for leaf in td_leaves:
        if leaf == root_node and len(td_graph.nodes()) > 1: # Don't trace path from root to itself unless it's the only node
            continue
        try:
            # In a tree, there's a unique simple path
            path = nx.shortest_path(td_graph, source=leaf, target=root_node)
            path_count += 1
            logging.info(f"Path from leaf {leaf} to trunk {root_node}:")
            if len(path) != 1:
                for i in range(len(path) - 1):
                    #print(f"  {path[i]}->{path[i+1]}")
                    edges__from_leaf_to_root[path[i]] = path[i+1] ## Store path edge
        except nx.NetworkXNoPath:
            logging.info(f"  No path found from leaf {leaf} to trunk {root_node} (TD might be disconnected).")
        except nx.NodeNotFound:
            logging.error(f"  Error: Node {leaf} or {root_node} not found in graph during path search.")
    
    if path_count == 0 and td_leaves and (len(td_graph.nodes()) > 1 or (len(td_graph.nodes())==1 and td_leaves[0] != root_node)):
        logging.info("No paths were printed (e.g. all leaves were the root, or errors occurred).")
    elif path_count == 0 and not td_leaves and len(td_graph.nodes()) > 0:
        logging.info("No leaves found, so no paths to print.")

def compute__graph():
    global td_graph
    global td_leaves
        
    # 4. Build TD graph and find paths from leaves to root/trunk
    if not td_bags: # Need bags (nodes) to build a graph
        logging.info("\nNo bags defined in TD, skipping path printing.")
        return
        
    td_graph = nx.Graph()
    if td_bags: # Add nodes only if bags were defined
        td_graph.add_nodes_from(td_bags.keys())
    td_graph.add_edges_from(td_edges)

    if not td_graph.nodes():
        logging.info("\nTD graph has no nodes, skipping path printing.")
        return
    
    if not nx.is_connected(td_graph) and len(td_graph.nodes()) > 1:
        logging.warning("\nWarning: The tree decomposition graph is not connected. Path finding might be incomplete.")
        # Could try to find paths within each connected component to a local "root" if desired.


    # Find leaves
    td_leaves = [node for node in td_graph.nodes() if td_graph.degree(node) == 1]
    if not td_leaves and len(td_graph.nodes()) == 1: # Single node graph
        td_leaves = [root_node] # The root is also a leaf
    elif not td_leaves and len(td_graph.nodes()) > 1: # No leaves in a multi-node graph (e.g. a cycle - not a tree)
        logging.warning("Warning: No leaves found in the TD graph (it might not be a tree). Path printing might be unusual.")
        # As a fallback, could pick all nodes except root as potential "leaves" for path demo
        # For now, let's proceed if leaves were identified.
    
    logging.info("\n--- Paths from Leaves to Trunk ---")
    if not td_leaves:
        logging.info("No leaves identified to trace paths from.")
    
def compute__root(root_bag_id_param=None):
    # Determine the root/trunk
    global root_node
    global td_graph
    
    if root_bag_id_param is not None:
        if root_bag_id_param in td_graph:
            root_node = root_bag_id_param
            logging.info(f"\nUsing specified root/trunk: {root_node}")
        else:
            logging.warning(f"Warning: Specified root ID {root_bag_id_param} not in TD. Choosing default root.")
            root_bag_id_param = None # Fallback to default

    if root_node is None:
        if td_graph.nodes():
            # Heuristic: pick node with smallest ID, or one with high degree, or just min ID.
            # Smallest ID is simple and deterministic.
            root_node = min(td_graph.nodes())
            logging.info(f"\nUsing default root/trunk (smallest bag ID): {root_node}")
        else:
            logging.info("\nCannot determine root, no nodes in TD graph.")
            return
        
def parse_decomposition(td_filepath):
    global td_bags 
    global td_edges
    
    # 2. Parse Tree Decomposition
    logging.info(f"\nParsing Tree Decomposition file: {td_filepath}...")
    td_bags, td_edges = parse_td_file(td_filepath)
    if td_bags is None:
        return
    if not td_bags and not td_edges:
        logging.info("No bags or edges found in TD file. Cannot proceed.")
        return
    if not td_bags and td_edges: # only edges, bags were inferred as empty
        logging.warning("Warning: TD file contained only edges. Bags were inferred as empty.")

    logging.info(f"Parsed {len(td_bags)} bags and {len(td_edges)} TD edges.")

    

    
def parse_problem(cnf_filepath):
    global clauses
    global num_vars
    global clauses_with_vars
    
    # 1. Parse CNF
    logging.info(f"Parsing CNF file: {cnf_filepath}...")
    num_vars, cnf_clauses = parse_cnf_dimacs(cnf_filepath)
    if cnf_clauses is None:
        return
    if not cnf_clauses:
        logging.warning("No clauses found in CNF file.")
        # Proceed if TD exists, but clause association part will be empty.

    # Preprocess clauses to get sets of variables involved (absolute values)
    # Store with original 0-based index
    clauses_with_vars = []
    for i, clause_literals in enumerate(cnf_clauses):
        vars_in_clause = {abs(lit) for lit in clause_literals if lit != 0}
        clauses_with_vars.append({'id': i, 'vars': vars_in_clause, 'literals': clause_literals})
    logging.info(f"Parsed {len(cnf_clauses)} clauses from CNF.")

    
def compute__bags_to_clauses():
    # 3. Associate clauses with bags
    global bag_to_clause_indices
    global clauses_with_vars
    

    # Iterate through each bag defined in the tree decomposition
    # Sorting bag IDs here is good for deterministic processing if order matters later,
    # but not strictly necessary for just building the map.
    # If td_bags might be empty, this loop won't run, which is fine.
    for bag_id, bag_vars_content in td_bags.items():
        # For each clause in the CNF
        for clause_info in clauses_with_vars: # clause_info is {'id': idx, 'vars': {var_ids}, 'literals': [...]}
            # Check if all variables in the current clause are a subset of variables in the current bag
            if clause_info['vars'].issubset(bag_vars_content):
                # If yes, associate this clause's ID with the current bag_id
                bag_to_clause_indices[bag_id].append(clause_info['id'])

    # Optional: Sort the clause indices within each bag's list for consistent output/processing
    for bag_id in bag_to_clause_indices:
        bag_to_clause_indices[bag_id].sort()        

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
        logging.error(f"Error: Input CNF file not found: {args.cnf_file}")
        return
    if not os.path.exists(args.td_file):
        logging.error(f"Error: Input .td file not found: {args.td_file}")
        return

    parse_problem(args.cnf_file)
    parse_decomposition(args.td_file)
    compute__bags_to_clauses()
    compute__graph()
    compute__root(args.root)
    compute__leaf_paths_to_root()
    compute__root_paths_to_leaves()


    print("DAG-FILE")
    print(f"NODES:{len(td_bags)}")
    print("GRAPH:")
    print_edge_map_with_source_clause_variables(edges__from_leaf_to_root)
    print("CLAUSES:")
    print_clauses_for_each_bag()
    print("REPORTING:")
    print(f"1-{num_vars}")
    
if __name__ == "__main__":
    main()
