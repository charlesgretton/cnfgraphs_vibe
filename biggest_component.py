import argparse
from collections import defaultdict, deque

def parse_td_for_components(td_filepath):
    """
    Parses a DIMACS Tree Decomposition file, focusing on bag structure for component analysis.
    Returns:
        - s_line_info: original s-line parameters as a tuple (num_bags, treewidth_plus_1, num_original_vertices)
        - bags: dict mapping bag_id (int) to a set of variables (int)
        - adj: adjacency list for bags (dict mapping bag_id to set of neighbor bag_ids)
        - comments: list of comment lines
    """
    s_line_info = None
    bags = {}
    adj = defaultdict(set)
    comments = []
    max_var_overall = 0 # To keep track of the universe of variables for the new s-line

    with open(td_filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith('c'):
                comments.append(line)
                continue
            
            parts = line.split()
            if not parts:
                continue

            if parts[0] == 's' and parts[1] == 'td':
                if len(parts) == 5:
                    s_line_info = (int(parts[2]), int(parts[3]), int(parts[4]))
                else:
                    raise ValueError(f"Malformed 's td' line: {line}")
            elif parts[0] == 'b':
                if len(parts) >= 2:
                    bag_id = int(parts[1])
                    bag_vars_list = [int(v) for v in parts[2:]]
                    bags[bag_id] = set(bag_vars_list)
                    if bag_vars_list:
                        current_max_var = max(bag_vars_list)
                        if current_max_var > max_var_overall:
                            max_var_overall = current_max_var
                else:
                    raise ValueError(f"Malformed 'b' line: {line}")
            else:
                # Assuming it's an edge line if not 's', 'b', or 'c'
                try:
                    u, v = int(parts[0]), int(parts[1])
                    adj[u].add(v)
                    adj[v].add(u)
                except (ValueError, IndexError):
                    print(f"Warning: Skipping unrecognized line in TD file: {line}")
                    
    if s_line_info is None:
        raise ValueError("TD file does not contain a valid 's td' line.")
    if not bags:
        print("Warning: No bags found in the TD file.")
        # Return a modified s_line_info if needed or handle appropriately
        return (0,0,0), {}, defaultdict(set), comments


    # If the original s-line num_original_vertices is larger, prefer that
    # This handles cases where the largest variable ID in the bags is smaller than the declared universe
    if s_line_info and s_line_info[2] > max_var_overall:
        max_var_overall = s_line_info[2]
        
    # Update s_line_info to use the determined max_var_overall if it's more accurate
    # or if the original was based on a larger universe than now present
    if s_line_info:
         s_line_info = (s_line_info[0], s_line_info[1], max_var_overall)


    return s_line_info, bags, adj, comments

def find_connected_components(nodes, adj):
    """
    Finds all connected components in a graph represented by an adjacency list.
    Args:
        nodes: A collection of all node IDs (e.g., bag IDs).
        adj: Adjacency list (dict mapping node_id to set of neighbor_node_ids).
    Returns:
        A list of sets, where each set contains the node IDs of a connected component.
    """
    visited = set()
    components = []
    
    for node in nodes:
        if node not in visited:
            component = set()
            q = deque([node])
            visited.add(node)
            component.add(node)
            
            while q:
                curr = q.popleft()
                for neighbor in adj.get(curr, []): # Use .get for nodes that might have no edges
                    if neighbor not in visited:
                        visited.add(neighbor)
                        component.add(neighbor)
                        q.append(neighbor)
            components.append(component)
            
    return components

def extract_largest_component_td(original_s_info, all_bags, all_adj, original_comments):
    """
    Extracts the largest connected component from the bag graph and prepares a new TD.
    """
    if not all_bags:
        print("No bags to process. Outputting an empty TD.")
        return (["c Input TD was empty or became empty."],
                "s td 0 0 0\n", {}, [])

    bag_ids = set(all_bags.keys())
    components = find_connected_components(bag_ids, all_adj)

    if not components:
        print("No components found (e.g., no bags or no edges). Outputting an empty TD.")
        return (["c No components found in the input TD."],
                "s td 0 0 0\n", {}, [])

    # Find the largest component by number of bags
    largest_component_bags_ids = max(components, key=len)
    
    print(f"Found {len(components)} connected component(s).")
    print(f"Largest component has {len(largest_component_bags_ids)} bags.")

    # --- Rebuild TD for the largest component ---
    
    # 1. Filter bags belonging to the largest component
    component_bags_temp = {
        bag_id: all_bags[bag_id] for bag_id in largest_component_bags_ids
    }

    # 2. Re-index bags in the largest component
    # Sort old bag IDs to make re-indexing deterministic
    old_ids_sorted = sorted(component_bags_temp.keys())
    
    new_component_bags = {}
    old_to_new_id_map = {}
    new_bag_id_counter = 1
    max_var_in_component = 0

    for old_id in old_ids_sorted:
        old_to_new_id_map[old_id] = new_bag_id_counter
        variables_in_bag = component_bags_temp[old_id]
        new_component_bags[new_bag_id_counter] = variables_in_bag
        if variables_in_bag:
            current_max_var_in_bag = max(variables_in_bag) if variables_in_bag else 0
            if current_max_var_in_bag > max_var_in_component:
                max_var_in_component = current_max_var_in_bag
        new_bag_id_counter += 1
    
    num_new_bags = len(new_component_bags)

    # 3. Reconstruct edges for the largest component using new bag IDs
    new_component_edges = []
    for old_bag_id in largest_component_bags_ids:
        if old_bag_id in old_to_new_id_map: # Should always be true
            new_u = old_to_new_id_map[old_bag_id]
            for old_neighbor_id in all_adj.get(old_bag_id, []):
                if old_neighbor_id in largest_component_bags_ids and old_neighbor_id in old_to_new_id_map:
                    new_v = old_to_new_id_map[old_neighbor_id]
                    # Add edge only if new_u < new_v to avoid duplicates and self-loops if u maps to v
                    if new_u < new_v:
                        new_component_edges.append((new_u, new_v))
    
    new_component_edges = sorted(list(set(new_component_edges))) # Ensure uniqueness and order

    # 4. Calculate new treewidth for the component
    new_treewidth = 0
    if new_component_bags:
        new_treewidth = max(len(bag_vars) for bag_vars in new_component_bags.values()) - 1
    if new_treewidth < 0: new_treewidth = 0

    # 5. Prepare new s-line
    # The number of original vertices should ideally be from the original problem context
    # We use max_var_in_component or the original s_line_info's value if it's more encompassing.
    num_original_vertices_for_s_line = original_s_info[2] if original_s_info else 0
    if max_var_in_component > num_original_vertices_for_s_line:
        num_original_vertices_for_s_line = max_var_in_component


    new_s_line = f"s td {num_new_bags} {new_treewidth + 1} {num_original_vertices_for_s_line}\n"

    new_comments = list(original_comments)
    new_comments.append("c Processed by script: extracted the largest connected component of bags.")
    new_comments.append(f"c Original TD had {original_s_info[0] if original_s_info else 'N/A'} bags, {len(components)} component(s).")
    new_comments.append(f"c Largest component (this output) has {num_new_bags} bags.")
    
    return new_comments, new_s_line, new_component_bags, new_component_edges

def write_td_output(output_filepath, comments, s_line, bags, edges):
    """
    Writes the tree decomposition to a file in DIMACS TD format.
    """
    with open(output_filepath, 'w') as f:
        for comment in comments:
            f.write(f"{comment}\n")
        f.write(s_line)
        
        for bag_id in sorted(bags.keys()):
            bag_vars_str = " ".join(map(str, sorted(list(bags[bag_id]))))
            f.write(f"b {bag_id} {bag_vars_str}\n")
            
        for u, v in sorted(edges):
            f.write(f"{u} {v}\n")
    print(f"Largest component TD written to: {output_filepath}")

def main():
    parser = argparse.ArgumentParser(
        description="Extracts the largest connected component (subtree of bags) "
                    "from a DIMACS tree decomposition file."
    )
    parser.add_argument("input_td_file", help="Path to the input DIMACS TD file (potentially disconnected).")
    parser.add_argument("output_td_file", help="Path for the output DIMACS TD file (largest component).")
    
    args = parser.parse_args()

    try:
        print(f"Parsing TD file: {args.input_td_file}")
        s_info, bags_data, adj_data, comments_data = parse_td_for_components(args.input_td_file)

        print("\nExtracting largest component...")
        new_comments, new_s_line, new_bags, new_edges = extract_largest_component_td(
            s_info, bags_data, adj_data, comments_data
        )
        
        write_td_output(args.output_td_file, new_comments, new_s_line, new_bags, new_edges)

    except FileNotFoundError as e:
        print(f"Error: File not found - {e.filename}")
    except ValueError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()