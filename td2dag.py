## Authors -- Gemini 2.5 Pro Preview 05-06
##         -- details, corrections and logging changes by Charles Gretton - May 15, 2025 

import argparse
import os
from collections import defaultdict
import networkx as nx
import logging
from collections import defaultdict, deque # <--- Make sure deque is imported here

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
edges__from_root_to_leaves = {}
bag_to_clause_indices = defaultdict(list) # I depart from Habet et al., and allow a clause to appear in multiple tree nodes (i.e., I do not exclude 'parent' clauses)

cnf_clauses = []
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
        
        print(f"{source_bag_id - 1}->{destination_bag_id - 1}:{vars_str}")


def format_integer_set_to_ranges(data_dict):
    """
    Takes a dictionary where values are sets of integers.
    For each set, it formats the integers into a comma-separated string
    with continuous ranges represented as "start-end".

    Args:
        data_dict (dict): A dictionary where keys are arbitrary and
                          values are sets of integers.

    Returns:
        dict: A new dictionary with the same keys, where values are
              the formatted strings.
    """
    formatted_dict = {}
    for key, int_set in data_dict.items():
        if not int_set:  # Handle empty sets
            formatted_dict[key] = ""
            continue

        # Sort the numbers to easily find ranges
        numbers = sorted(list(int_set))
        
        ranges = []
        if not numbers: # Should be caught by `if not int_set` but good for robustness
            formatted_dict[key] = ""
            continue

        start_of_range = numbers[0]
        
        for i in range(1, len(numbers)):
            # If the current number is not consecutive to the previous one
            if numbers[i] != numbers[i-1] + 1:
                # Finalize the previous range
                if start_of_range == numbers[i-1]:
                    ranges.append(str(start_of_range))
                else:
                    ranges.append(f"{start_of_range}-{numbers[i-1]}")
                # Start a new range
                start_of_range = numbers[i]
        
        # Add the last range
        if start_of_range == numbers[-1]:
            ranges.append(str(start_of_range))
        else:
            ranges.append(f"{start_of_range}-{numbers[-1]}")
            
        formatted_dict[key] = ",".join(ranges)
        
    return formatted_dict

def format_aggregated_integers_to_ranges(data_dict):
    """
    Aggregates all integers from all sets in the input dictionary into a single set,
    then formats this aggregated set into a comma-separated string
    with continuous ranges represented as "start-end".

    Args:
        data_dict (dict): A dictionary where keys are arbitrary and
                          values are sets of integers.

    Returns:
        str: A comma-separated string representing the aggregated integers
             with ranges, or an empty string if no integers are found.
    """
    aggregated_set = set()

    # 1. Aggregate all integers into a single set
    for key, int_set in data_dict.items():
        if int_set: # Ensure the set is not None or empty before updating
            aggregated_set.update(int_set)

    if not aggregated_set:  # Handle case where no integers were found at all
        return ""

    # 2. Format the aggregated set into ranges (same logic as before)
    numbers = sorted(list(aggregated_set))
    
    ranges = []
    # This check is technically redundant if `if not aggregated_set` above is hit,
    # but good for standalone use of this part of the logic.
    if not numbers: 
        return ""

    start_of_range = numbers[0]
    
    for i in range(1, len(numbers)):
        if numbers[i] != numbers[i-1] + 1:
            if start_of_range == numbers[i-1]:
                ranges.append(str(start_of_range))
            else:
                ranges.append(f"{start_of_range}-{numbers[i-1]}")
            start_of_range = numbers[i]
    
    # Add the last range
    if start_of_range == numbers[-1]:
        ranges.append(str(start_of_range))
    else:
        ranges.append(f"{start_of_range}-{numbers[-1]}")
            
    return ",".join(ranges)

variables_cumulation = {} # This will store bag_id -> set of cumulative variables
already_printed=set()

def print_edge_map_with_cumulative_variables(input_edge_map, current_nodes,doprint=True):
    """
    Recursively processes nodes in a tree-like structure (defined by input_edge_map)
    to compute cumulative variables for each node.

    Args:
        input_edge_map: A dictionary representing directed edges, e.g., {parent: child}.
                        If it's {child: parent}, the logic for "destinations" needs adjustment.
                        Assuming for now it's {source_node: destination_node} or
                        if it's a parent-to-children map {parent: [child1, child2]}, the
                        looping needs to be adjusted.
                        Based on your usage `destination = input_edge_map[n]`, it seems
                        like a map from a node to its single successor/child in a path,
                        or from a child to its parent if `roots` are leaves.
        current_nodes: A collection (e.g., list or set) of nodes to process in this iteration.
    """
    global variables_cumulation
    global bag_to_clause_indices # Needs to be accessible
    global clauses_with_vars   # Needs to be accessible
    global already_printed
    
    if not current_nodes: # Base case for recursion
        return

    next_level_nodes = set()

    for node_id in current_nodes:
        # 1. Calculate variables directly associated with this node/bag
        current_node_variables = set()
        if node_id in bag_to_clause_indices: # Check if the node_id is a valid bag
            logging.info(f"Processing {node_id}")
            for clause_index in bag_to_clause_indices[node_id]:
                if clause_index < len(clauses_with_vars): # Ensure clause_index is valid
                    for literal in clauses_with_vars[clause_index]['vars']:
                        
                        current_node_variables.add(abs(literal)) # Use add for sets
                else:
                    logging.error(f"Clause index {clause_index} for bag {node_id} is out of bounds for clauses_with_vars.")
        else:
            logging.info(f"Bag ID {node_id} not found in bag_to_clause_indices.")


        # 2. Initialize or update variables_cumulation for the current node
        if node_id not in variables_cumulation:
            variables_cumulation[node_id] = set()
        
        # Add the variables directly from this node's clauses
        variables_cumulation[node_id].update(current_node_variables) # Use update to add multiple elements

        # 3. Process children/successors
        # This part heavily depends on the structure of input_edge_map
        # Assuming input_edge_map[parent] = child or input_edge_map[node] = next_node_in_path
        
        if node_id in input_edge_map:
            # Safely get destination(s)
            destinations_for_node = input_edge_map[node_id]
            if not isinstance(destinations_for_node, (list, set, tuple)):
                destinations_for_node = [destinations_for_node] # Make it iterable

            for dest_node_id in destinations_for_node:
                logging.info(f"Successor is {dest_node_id}")
                if dest_node_id not in variables_cumulation:
                    variables_cumulation[dest_node_id] = set()

                to_print=format_aggregated_integers_to_ranges(variables_cumulation)

                if doprint:
                    if (node_id-1,dest_node_id-1) not in already_printed:
                        print(f"{node_id-1}->{dest_node_id-1}:{to_print}")
                        already_printed.add( (node_id-1,dest_node_id-1) );
                    
                # Crucially, the cumulative variables from the parent (node_id)
                # are added to the child (dest_node_id)
                variables_cumulation[dest_node_id].update(variables_cumulation[node_id])
                next_level_nodes.add(dest_node_id)
        


    # Recursive call for the next level of nodes
    if next_level_nodes:
        print_edge_map_with_cumulative_variables(input_edge_map, list(next_level_nodes))

def print_edge_map_with_cumulative_variables__OLD(input_edge_map, map_name="Edge Map with Cumulative Variables", roots=None):
    """
    Prints edges from an input_edge_map. For each edge A->B,
    the variables printed are the cumulative variables from A and all its
    ancestors on the current path from a root.

    Args:
        input_edge_map (dict): A dictionary where keys are source bag IDs
                               and values are lists of destination bag IDs
                               (or a single ID if each source has one successor).
                               Example: {1: [2, 3], 2: [4]} or {1:2, 2:4}
        map_name (str): A descriptive name for the map.
        roots (list, optional): A list of starting node IDs. If None,
                                 nodes that are sources but not destinations
                                 in input_edge_map will be considered roots.
    """
    global bag_to_clause_indices
    global clauses_with_vars

    logging.info(f"\n--- {map_name} ---")

    if not input_edge_map:
        logging.warning(f"The provided '{map_name}' is empty. Nothing to print.")
        return

    # For clarity and flexibility, let's ensure the input_edge_map values are lists
    # This handles both source:dest and source:[dest1, dest2]
    adj = defaultdict(list)
    all_nodes_in_map = set()
    for s, d_val in input_edge_map.items():
        all_nodes_in_map.add(s)
        if isinstance(d_val, list):
            adj[s].extend(d_val)
            all_nodes_in_map.update(d_val)
        else: # Assuming d_val is a single destination
            adj[s].append(d_val)
            all_nodes_in_map.add(d_val)
    
    if not adj and all_nodes_in_map: # Only nodes, no edges in map
        logging.warning(f"The provided '{map_name}' contains nodes but no traversable edges. Printing node variables only.")
        for node_id in sorted(list(all_nodes_in_map)):
            current_node_vars = set()
            if node_id in bag_to_clause_indices:
                for clause_id in bag_to_clause_indices[node_id]:
                    if 0 <= clause_id < len(clauses_with_vars):
                        current_node_vars.update(clauses_with_vars[clause_id]['vars'])
            vars_str = ",".join(map(str, sorted(list(current_node_vars))))
            # Adjusting print format since there's no "edge"
            print(f"Node {node_id-1} (variables: {vars_str})")
        return
    elif not adj:
        logging.warning(f"The provided '{map_name}' is effectively empty. Nothing to print.")
        return


    # Determine roots if not provided
    if roots is None:
        sources = set(adj.keys())
        destinations = set()
        for dest_list in adj.values():
            destinations.update(dest_list)
        roots = list(sources - destinations)
        if not roots and adj: # Possible cycle or all nodes are destinations
            # Fallback: pick the numerically smallest source node as a pseudo-root if any edge exists
            if sources:
                roots = [min(sources)]
                logging.warning(f"No clear roots found (e.g., cycles might exist). Starting traversal from node {roots[0]}.")
            else: # adj is empty
                 logging.warning(f"The provided '{map_name}' has no edges. Nothing to print.")
                 return


    if not roots:
        logging.warning(f"No root nodes identified or provided for '{map_name}'. Cannot perform traversal.")
        return

    logging.info(f"Starting traversal from root(s): {roots}")
    
    # Keep track of printed edges to avoid re-printing in case of DAGs (not just trees)
    # or multiple paths leading to the same information accumulation.
    # The key is (source, dest), value is the set of cumulative vars printed for it.
    printed_cumulative_edges = {}

    for root_node_id in roots:
        # Queue for BFS-like traversal: (current_node_id, accumulated_variables_set_from_ancestors)
        queue = deque([(root_node_id, set())])
        # Visited set for current traversal from THIS root to handle cycles within its reach
        # Stores (node, frozenset(accumulated_vars)) to distinguish paths if vars differ
        visited_in_bfs = set() 

        while queue:
            current_node, inherited_vars = queue.popleft()

            # Check if we've visited this node via the exact same accumulated variable set path
            # This helps break cycles or redundant paths if the accumulation state is the same.
            current_state = (current_node, frozenset(inherited_vars))
            if current_state in visited_in_bfs:
                continue
            visited_in_bfs.add(current_state)

            # Get variables from clauses directly associated with the current_node
            current_node_clause_vars = set()
            if current_node in bag_to_clause_indices:
                for clause_id in bag_to_clause_indices[current_node]:
                    if 0 <= clause_id < len(clauses_with_vars):
                        current_node_clause_vars.update(clauses_with_vars[clause_id]['vars'])
                    else:
                        logging.warning(f"Clause ID {clause_id} (from bag {current_node}) out of range.")
            
            # The new cumulative set of variables for this node and its children
            vars_for_current_and_children = inherited_vars.union(current_node_clause_vars)

            # Process outgoing edges from current_node
            if current_node in adj:
                for neighbor_node in adj[current_node]:
                    edge = (current_node, neighbor_node)
                    
                    # The variables to print for THIS edge are those accumulated *up to and including* the source (current_node)
                    cumulative_vars_for_this_edge_print = vars_for_current_and_children 
                                                       # or inherited_vars.union(current_node_clause_vars)

                    # Check if we've already printed this edge with this exact (or a superset of) cumulative variable set
                    # This is tricky. For simplicity, if an edge is printed once, we might not print it again,
                    # or we print it if the cumulative set is different/larger.
                    # Let's print if the edge itself is new in the context of `printed_cumulative_edges`.
                    # If an edge (A,B) is printed, the vars are those of A and its ancestors.
                    
                    # If you want to ensure an edge is printed only ONCE globally, irrespective of path:
                    if edge not in printed_cumulative_edges:
                        vars_str = ",".join(map(str, sorted(list(cumulative_vars_for_this_edge_print))))
                        print(f"{current_node-1}->{neighbor_node-1}:{vars_str}") # Assuming 0-indexed print
                        printed_cumulative_edges[edge] = cumulative_vars_for_this_edge_print
                    # Else: If you want to print if the cumulative set is NEW for this edge (more complex output):
                    # elif printed_cumulative_edges.get(edge) != cumulative_vars_for_this_edge_print:
                    #     vars_str = ",".join(map(str, sorted(list(cumulative_vars_for_this_edge_print))))
                    #     print(f"{current_node-1}->{neighbor_node-1}:{vars_str} (Updated set)")
                    #     printed_cumulative_edges[edge] = cumulative_vars_for_this_edge_print


                    # Add neighbor to queue with the updated cumulative variables
                    # The variables inherited by the neighbor are those accumulated up to current_node
                    queue.append((neighbor_node, vars_for_current_and_children))


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

        if 0 == len(clause_indices_str):
            print(f"{bag_id-1}:{len(clauses_with_vars)}")
        else:
            print(f"{bag_id-1}:{clause_indices_str}")

    if not sorted_bag_ids: # Second check if td_bags became empty after sorting (shouldn't happen)
        logging.info("No bag IDs found to process.")


def compute__root_paths_to_leaves():
    global td_bags, td_edges, root_node, td_graph, td_leaves, edges__from_root_to_leaves
    
    # Ensure necessary globals are initialized
    if td_leaves is None or root_node is None or not td_graph.nodes():
        logging.error("Error: TD graph, leaves, or root_node not initialized for compute__root_paths_to_leaves.")
        return

    # Clear the dictionary before populating, in case this function is called multiple times
    edges__from_root_to_leaves.clear()
    
    path_count = 0
    logging.info(f"Computing paths from root {root_node} to leaves: {td_leaves}")

    for leaf in td_leaves:
        if leaf == root_node and len(td_graph.nodes()) == 1: # Path from root to itself if it's the only node
            # No edges to add in this case for edges__from_root_to_leaves
            logging.info(f"  Path from root {root_node} to leaf {leaf} (is the same node).")
            path_count +=1
            continue
        if leaf == root_node and len(td_graph.nodes()) > 1: # Root cannot be a leaf if there are other nodes
            continue

        try:
            # Find the path from the root to the current leaf
            path = nx.shortest_path(td_graph, source=root_node, target=leaf)
            path_count += 1
            logging.info(f"  Path from root {root_node} to leaf {leaf}: {path}") # For debugging

            if len(path) > 1: # Path has at least one edge
                for i in range(len(path) - 1):
                    # path[i] is closer to the root (source)
                    # path[i+1] is further from the root, towards the leaf (destination)
                    current_source = path[i]
                    current_destination = path[i+1]
                    
                    # If you want to store multiple children for a source:
                    if current_source not in edges__from_root_to_leaves:
                        edges__from_root_to_leaves[current_source] = []
                    if current_destination not in edges__from_root_to_leaves[current_source]:
                        edges__from_root_to_leaves[current_source].append(current_destination)
                    
                    # If sticking to source:destination (overwrites if source has multiple children on different paths)
                    ## edges__from_root_to_leaves[current_source] = current_destination

                    if len(path) - 1 == i+1:
                        edges__from_root_to_leaves[current_destination] = len(td_bags) + 1
                    
        except nx.NetworkXNoPath:
            # This should ideally not happen if leaves are reachable from root in a tree
            logging.info(f"  No path found from root {root_node} to leaf {leaf} (TD might be disconnected or root not an ancestor).")
        except nx.NodeNotFound:
            logging.error(f"  Error: Node {root_node} or {leaf} not found in graph during path search.")
            
    # print(f"Processed {path_count} paths from root. Populated edges__from_root_to_leaves.")


    
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
    global cnf_clauses
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
    global clauses
    global root_node
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
    
    parser.add_argument('--toroot', action='store_true', help='Traverse from root to leaves')

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


    if args.toroot:
        print("DAG-FILE")
        print(f"NODES:{len(td_bags)}")
        print("GRAPH:")
        logging.info(f"{edges__from_leaf_to_root}")
        logging.info(f"Root node is: {root_node}")
        print_edge_map_with_cumulative_variables(edges__from_leaf_to_root,td_leaves,False)
        print_edge_map_with_cumulative_variables(edges__from_leaf_to_root,td_leaves,True)
        print("CLAUSES:")
        print_clauses_for_each_bag()
        print("REPORTING:")
        print(f"1-{num_vars}")
    else:
        print("DAG-FILE")
        print(f"NODES:{len(td_bags)+1}")
        print("GRAPH:")
        logging.info(f"{edges__from_root_to_leaves}")
        logging.info(f"Root node is: {root_node}")
        print_edge_map_with_cumulative_variables(edges__from_root_to_leaves,[root_node],True)
        print("CLAUSES:")
        print_clauses_for_each_bag()
        print(f"{len(td_bags)}:0-{len(cnf_clauses)-1}")
        print("REPORTING:")
        print(f"1-{num_vars}")
        
    
if __name__ == "__main__":
    main()
