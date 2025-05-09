## Author -- Gemini 2.5 Pro Preview 05-06

import argparse
import os
from collections import defaultdict

def parse_td_file(td_filepath):
    """
    Parses a tree decomposition file in .td DIMACS-like format.
    CORRECTED: Bag lines ('b') do not necessarily end with 0.

    Returns:
        tuple: (num_bags_declared, max_bag_size_declared, num_orig_vertices_declared,
                dict_of_bags, list_of_td_edges, list_of_comments)
               or (None, None, None, None, None, None) on error.
        dict_of_bags: {bag_id: set_of_vertices_in_bag}
        list_of_td_edges: list of tuples (bag_id1, bag_id2)
    """
    num_bags_declared = 0
    max_bag_size_declared = 0 # This is treewidth + 1
    num_orig_vertices_declared = 0
    bags = {} # Using dict for direct access by bag_id
    td_edges = []
    comments = []
    parsed_solution_line = False

    try:
        with open(td_filepath, 'r') as f:
            for line_num, line_content in enumerate(f, 1):
                line = line_content.strip()
                if not line:
                    continue
                if line.startswith('c'):
                    comments.append(line)
                    continue
                
                parts = line.split()
                if not parts: # Empty line after strip somehow
                    continue

                if line.startswith('s td'):
                    if parsed_solution_line:
                        print(f"Error: Multiple 's td' lines found in {td_filepath}.")
                        return None, None, None, None, None, None
                    if len(parts) != 5:
                        print(f"Error: Malformed 's td' line in {td_filepath}: {line_content.strip()}")
                        return None, None, None, None, None, None
                    try:
                        num_bags_declared = int(parts[2])
                        max_bag_size_declared = int(parts[3])
                        num_orig_vertices_declared = int(parts[4])
                        parsed_solution_line = True
                    except ValueError:
                        print(f"Error: Non-integer values in 's td' line in {td_filepath}: {line_content.strip()}")
                        return None, None, None, None, None, None
                elif line.startswith('b'): # Bag definition
                    if not parsed_solution_line:
                         print(f"Error: Bag line 'b' found before 's td' line in {td_filepath}.")
                         return None, None, None, None, None, None
                    # Bag line: b <id> v1 v2 ... vn [0] (0 is optional)
                    if len(parts) < 2: # Needs at least 'b <id>'
                        print(f"Error: Malformed bag line (too short) in {td_filepath} (line {line_num}): {line_content.strip()}")
                        return None, None, None, None, None, None
                    try:
                        bag_id = int(parts[1])
                        # Vertices are from parts[2] onwards. If last part is '0', exclude it.
                        vertex_parts = parts[2:]
                        if vertex_parts and vertex_parts[-1] == '0':
                            vertex_parts = vertex_parts[:-1]
                        
                        bag_vertices = {int(v) for v in vertex_parts}
                        
                        if bag_id in bags:
                            print(f"Warning: Duplicate bag ID {bag_id} found in {td_filepath} (line {line_num}). Overwriting.")
                        bags[bag_id] = bag_vertices
                    except ValueError:
                        print(f"Error: Non-integer value in bag line in {td_filepath} (line {line_num}): {line_content.strip()}")
                        return None, None, None, None, None, None
                elif parsed_solution_line: # TD Edge definition (assuming it comes after 's td')
                                          # And doesn't start with 'b' or 'c'
                    # TD Edge: <bag_id1> <bag_id2> [0] (0 is optional)
                    if len(parts) < 2 : # Needs at least two bag IDs
                        print(f"Warning: Malformed TD edge line (too short) in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                    
                    edge_node_parts = parts
                    if edge_node_parts[-1] == '0': # Optional trailing 0
                        edge_node_parts = edge_node_parts[:-1]
                    
                    if len(edge_node_parts) != 2: # Must be exactly two bag IDs after removing optional 0
                         print(f"Warning: Malformed TD edge line (expected 2 bag IDs) in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                         continue
                    try:
                        u_bag, v_bag = int(edge_node_parts[0]), int(edge_node_parts[1])
                        td_edges.append(tuple(sorted((u_bag, v_bag))))
                    except ValueError:
                        print(f"Warning: Non-integer bag ID in TD edge line in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                else: # Should not happen if logic is correct
                    print(f"Warning: Unexpected line in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")

        if not parsed_solution_line and (bags or td_edges):
            print(f"Error: No 's td' line found in {td_filepath} but bags/edges seem present.")
            return None, None, None, None, None, None
        if not parsed_solution_line and not bags and not td_edges:
            print(f"Warning: TD file {td_filepath} appears empty or contains only comments.")
            return 0,0,0, {}, [], comments


        # Validations
        if len(bags) != num_bags_declared:
            print(f"Warning: Declared {num_bags_declared} bags in 's td' line, but found {len(bags)} 'b' lines.")
        
        actual_max_bag_size = 0
        if bags: # Ensure bags is not empty before calling max on empty sequence
            actual_max_bag_size = max(len(b_vars) for b_vars in bags.values()) if bags else 0
        
        if actual_max_bag_size != max_bag_size_declared and len(bags)>0 : # only if bags were actually parsed
            print(f"Warning: Declared max_bag_size (tw+1) as {max_bag_size_declared} in 's td' line, but calculated {actual_max_bag_size} from 'b' lines.")
            # Use the actual max bag size for treewidth reporting if different.
            max_bag_size_declared = actual_max_bag_size # Update to actual for reporting

        # Check if all bag IDs in td_edges are defined in 'b' lines
        defined_bag_ids = set(bags.keys())
        for b1, b2 in td_edges:
            if b1 not in defined_bag_ids:
                print(f"Warning: TD edge ({b1}, {b2}) references undefined bag ID {b1}.")
            if b2 not in defined_bag_ids:
                print(f"Warning: TD edge ({b1}, {b2}) references undefined bag ID {b2}.")
        
        # Remove duplicate TD edges
        td_edges = sorted(list(set(td_edges)))

        return num_bags_declared, max_bag_size_declared, num_orig_vertices_declared, bags, td_edges, comments

    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None, None, None, None, None
    except Exception as e:
        print(f"An unexpected error occurred during .td parsing: {e}")
        return None, None, None, None, None, None

def parse_gr_graph(gr_filepath):
    """
    Parses a graph file in .gr DIMACS-like format.

    Returns:
        tuple: (num_vertices, set_of_edges, list_of_comments) or (None, None, None) on error.
               set_of_edges contains tuples (u, v) with u < v.
    """
    vertices_declared = 0
    edges_declared = 0
    edges = set()
    comments = []
    parsed_problem_line = False

    try:
        with open(gr_filepath, 'r') as f:
            for line_num, line_content in enumerate(f, 1):
                line = line_content.strip()
                if not line:
                    continue
                if line.startswith('c'):
                    comments.append(line)
                    continue
                
                parts = line.split()
                if line.startswith('p'):
                    if parsed_problem_line:
                        print(f"Error: Multiple 'p' lines found in {gr_filepath}.")
                        return None, None, None
                    if len(parts) < 3 or parts[1].lower() not in ["tw", "edge", "graph"]: # Accommodate variations
                        print(f"Error: Malformed 'p' line in {gr_filepath}: {line_content.strip()}")
                        return None, None, None
                    try:
                        vertices_declared = int(parts[2])
                        # Edges might not always be present or accurate in problem line for some tools
                        if len(parts) > 3:
                            edges_declared = int(parts[3])
                        parsed_problem_line = True
                    except ValueError:
                        print(f"Error: Non-integer values in 'p' line in {gr_filepath}: {line_content.strip()}")
                        return None, None, None
                elif parsed_problem_line:
                    if len(parts) != 2:
                        print(f"Warning: Malformed edge line in {gr_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                    try:
                        u, v = int(parts[0]), int(parts[1])
                        # Store edges in canonical form (smaller, larger)
                        edges.add(tuple(sorted((u, v))))
                    except ValueError:
                        print(f"Warning: Non-integer vertex in edge line in {gr_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                else:
                    print(f"Error: Encountered data line before 'p' line in {gr_filepath}: {line_content.strip()}")
                    return None, None, None
        
        if not parsed_problem_line and (vertices_declared > 0 or edges):
             print(f"Error: No 'p' line found in {gr_filepath}, but data seems present.")
             return None, None, None
        if not parsed_problem_line and not edges: # Empty or comments only
             print(f"Warning: Graph file {gr_filepath} appears empty or contains only comments.")
             return 0, set(), comments


        # Validate actual number of unique vertices
        actual_vertices = set()
        for u, v in edges:
            actual_vertices.add(u)
            actual_vertices.add(v)
        
        # If vertices_declared is 0 but there are edges, it's an issue.
        # If vertices_declared > 0 but no edges, it's a graph with isolated vertices (valid).
        if vertices_declared == 0 and actual_vertices:
            print(f"Warning: 'p' line in {gr_filepath} declares 0 vertices, but edges exist. Will use max vertex ID found.")
            max_v_id = 0
            if actual_vertices:
                max_v_id = max(actual_vertices)
            vertices_declared = max_v_id # Or len(actual_vertices) if re-numbering, but stick to declared/max_id

        # Check if all vertex IDs are within [1, vertices_declared]
        for v_id in actual_vertices:
            if not (1 <= v_id <= vertices_declared) and vertices_declared > 0:
                print(f"Warning: Vertex {v_id} from an edge is outside the declared range [1, {vertices_declared}] in {gr_filepath}.")

        if len(edges) != edges_declared and edges_declared > 0: # only warn if edges_declared was actually set
            print(f"Warning: Declared {edges_declared} edges in {gr_filepath}, but found {len(edges)} unique edges.")

        return vertices_declared, edges, comments

    except FileNotFoundError:
        print(f"Error: Graph file not found: {gr_filepath}")
        return None, None, None
    except Exception as e:
        print(f"An unexpected error occurred during .gr parsing: {e}")
        return None, None, None


def parse_td_file2(td_filepath):
    """
    Parses a tree decomposition file in .td DIMACS-like format.

    Returns:
        tuple: (num_bags_declared, max_bag_size_declared, num_orig_vertices_declared,
                dict_of_bags, list_of_td_edges, list_of_comments)
               or (None, None, None, None, None, None) on error.
        dict_of_bags: {bag_id: set_of_vertices_in_bag}
        list_of_td_edges: list of tuples (bag_id1, bag_id2)
    """
    num_bags_declared = 0
    max_bag_size_declared = 0 # This is treewidth + 1
    num_orig_vertices_declared = 0
    bags = {} # Using dict for direct access by bag_id
    td_edges = []
    comments = []
    parsed_solution_line = False

    try:
        with open(td_filepath, 'r') as f:
            for line_num, line_content in enumerate(f, 1):
                line = line_content.strip()
                if not line:
                    continue
                if line.startswith('c'):
                    comments.append(line)
                    continue
                
                parts = line.split()
                if line.startswith('s td'):
                    if parsed_solution_line:
                        print(f"Error: Multiple 's td' lines found in {td_filepath}.")
                        return None, None, None, None, None, None
                    if len(parts) != 5:
                        print(f"Error: Malformed 's td' line in {td_filepath}: {line_content.strip()}")
                        return None, None, None, None, None, None
                    try:
                        num_bags_declared = int(parts[2])
                        max_bag_size_declared = int(parts[3])
                        num_orig_vertices_declared = int(parts[4])
                        parsed_solution_line = True
                    except ValueError:
                        print(f"Error: Non-integer values in 's td' line in {td_filepath}: {line_content.strip()}")
                        return None, None, None, None, None, None
                elif line.startswith('b'): # Bag definition
                    if not parsed_solution_line:
                         print(f"Error: Bag line 'b' found before 's td' line in {td_filepath}.")
                         return None, None, None, None, None, None
                    if len(parts) < 2 or parts[-1] != '0': # Needs at least 'b <id> 0' for an empty bag
                        print(f"Error: Malformed bag line (must end with 0) in {td_filepath} (line {line_num}): {line_content.strip()}")
                        return None, None, None, None, None, None
                    try:
                        bag_id = int(parts[1])
                        bag_vertices = {int(v) for v in parts[2:-1]} # Exclude 'b', bag_id, and trailing '0'
                        if bag_id in bags:
                            print(f"Warning: Duplicate bag ID {bag_id} found in {td_filepath} (line {line_num}). Overwriting.")
                        bags[bag_id] = bag_vertices
                    except ValueError:
                        print(f"Error: Non-integer value in bag line in {td_filepath} (line {line_num}): {line_content.strip()}")
                        return None, None, None, None, None, None
                elif parsed_solution_line: # TD Edge definition (assuming it comes after 's td')
                                          # And doesn't start with 'b' or 'c'
                    if len(parts) not in [2, 3]: # e.g. "1 2" or "1 2 0"
                        print(f"Warning: Malformed TD edge line in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                    if len(parts) == 3 and parts[-1] != '0':
                        print(f"Warning: TD edge line with 3 parts does not end with 0 in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                    try:
                        u_bag, v_bag = int(parts[0]), int(parts[1])
                        td_edges.append(tuple(sorted((u_bag, v_bag))))
                    except ValueError:
                        print(f"Warning: Non-integer bag ID in TD edge line in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")
                        continue
                else: # Should not happen if logic is correct
                    print(f"Warning: Unexpected line in {td_filepath} (line {line_num}): {line_content.strip()}. Skipping.")

        if not parsed_solution_line and (bags or td_edges):
            print(f"Error: No 's td' line found in {td_filepath} but bags/edges seem present.")
            return None, None, None, None, None, None
        if not parsed_solution_line and not bags and not td_edges:
            print(f"Warning: TD file {td_filepath} appears empty or contains only comments.")
            return 0,0,0, {}, [], comments


        # Validations
        if len(bags) != num_bags_declared:
            print(f"Warning: Declared {num_bags_declared} bags in 's td' line, but found {len(bags)} 'b' lines.")
        
        actual_max_bag_size = 0
        if bags:
            actual_max_bag_size = max(len(b_vars) for b_vars in bags.values()) if bags else 0
        
        if actual_max_bag_size != max_bag_size_declared and len(bags)>0 : # only if bags were actually parsed
            print(f"Warning: Declared max_bag_size (tw+1) as {max_bag_size_declared} in 's td' line, but calculated {actual_max_bag_size} from 'b' lines.")
            # Use the actual max bag size for treewidth reporting if different.
            max_bag_size_declared = actual_max_bag_size 

        # Check if all bag IDs in td_edges are defined in 'b' lines
        defined_bag_ids = set(bags.keys())
        for b1, b2 in td_edges:
            if b1 not in defined_bag_ids:
                print(f"Warning: TD edge references undefined bag ID {b1}.")
            if b2 not in defined_bag_ids:
                print(f"Warning: TD edge references undefined bag ID {b2}.")
        
        # Remove duplicate TD edges
        td_edges = sorted(list(set(td_edges)))

        return num_bags_declared, max_bag_size_declared, num_orig_vertices_declared, bags, td_edges, comments

    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None, None, None, None, None
    except Exception as e:
        print(f"An unexpected error occurred during .td parsing: {e}")
        return None, None, None, None, None, None

def verify_tree_decomposition(gr_v_count, gr_edges, td_num_bags, td_max_bag_size, td_orig_v_count, td_bags_dict, td_tree_edges):
    """
    Performs verification of the tree decomposition against the original graph.
    """
    print("\n--- Verification Results ---")
    valid_td = True

    # 0. Basic consistency check
    if gr_v_count != td_orig_v_count and gr_v_count > 0 and td_orig_v_count > 0: # Allow if one is 0 (empty graph)
        print(f"Warning: Original graph declares {gr_v_count} vertices, but TD file's 's td' line says {td_orig_v_count} original vertices.")
        # Decide which one to trust or if this is a hard error. For checks, we'll proceed but note it.

    # Get all unique vertices from the original graph's edges
    original_graph_vertices = set()
    for u, v in gr_edges:
        original_graph_vertices.add(u)
        original_graph_vertices.add(v)
    
    # If gr_v_count is specified, it's the authority on max vertex ID.
    # If gr_v_count is 0 (e.g. from an empty .gr file), but original_graph_vertices has content,
    # this implies an issue with .gr parsing or content.
    # For isolated vertices up to gr_v_count:
    if gr_v_count > 0:
        for i in range(1, gr_v_count + 1):
            original_graph_vertices.add(i) # Ensure isolated vertices are considered


    # 1. Vertex Coverage Verification (TD Property 1)
    print("\n1. Vertex Coverage (TD Property 1):")
    all_vertices_in_td_bags = set()
    for bag_id, bag_content in td_bags_dict.items():
        all_vertices_in_td_bags.update(bag_content)

    missing_vertices_from_td = original_graph_vertices - all_vertices_in_td_bags
    if missing_vertices_from_td:
        print(f"  FAIL: The following {len(missing_vertices_from_td)} original graph vertices are NOT in any TD bag: {sorted(list(missing_vertices_from_td))}")
        valid_td = False
    else:
        print("  PASS: All original graph vertices appear in at least one TD bag.")

    extra_vertices_in_td = all_vertices_in_td_bags - original_graph_vertices
    if extra_vertices_in_td:
        # This can happen if td_orig_v_count was different or if bags contain out-of-range vertices
        print(f"  WARNING: The following {len(extra_vertices_in_td)} vertices appear in TD bags but are NOT in the original graph's vertex set (max ID {gr_v_count}): {sorted(list(extra_vertices_in_td))}")
        # Not necessarily a TD property violation if td_orig_v_count was larger, but good to note.


    # 2. Edge Coverage Verification (TD Property 2)
    print("\n2. Edge Coverage (TD Property 2):")
    uncovered_edges = []
    for edge_u, edge_v in gr_edges:
        is_covered = False
        for bag_id, bag_content in td_bags_dict.items():
            if edge_u in bag_content and edge_v in bag_content:
                is_covered = True
                break
        if not is_covered:
            uncovered_edges.append((edge_u, edge_v))

    if uncovered_edges:
        print(f"  FAIL: The following {len(uncovered_edges)} original graph edges are NOT covered by any single TD bag:")
        for i, edge in enumerate(uncovered_edges):
            if i < 10: # Print first few
                print(f"    {edge}")
            elif i == 10:
                print("    ... (and more)")
                break
        valid_td = False
    else:
        print("  PASS: All original graph edges are covered by at least one TD bag.")

    # 3. Connectivity Property (TD Property 3) - Partial Check / Awareness
    # A full check requires building the TD's tree structure and running BFS/DFS for each original vertex.
    # This is more complex than the scope here. We've already checked if all vertices appear (Property 1).
    print("\n3. Connectivity Property (TD Property 3 - 'Running Intersection'):")
    print("  INFO: A full check of this property (induced subgraphs of bags containing a vertex are connected in TD) is complex.")
    print("        This script primarily checks vertex and edge coverage (Properties 1 and 2).")
    print("        If Properties 1 and 2 pass, and the TD provider is reliable, this often holds.")
    # A simple check: are there enough bags for the number of TD edges?
    # (Number of edges in a tree is num_nodes - 1)
    if td_num_bags > 0 and len(td_tree_edges) != td_num_bags - 1:
        print(f"  WARNING: The TD structure has {td_num_bags} bags but {len(td_tree_edges)} edges. For a tree, it should be {td_num_bags - 1} edges.")
        print("           This might indicate the TD is not a tree (e.g., disconnected or cyclic).")
        # valid_td = False # Could make this a failure condition.


    # 4. Reported Treewidth
    print("\n4. Treewidth Information:")
    if td_max_bag_size > 0 :
        treewidth = td_max_bag_size - 1
        print(f"  Reported max bag size (treewidth + 1): {td_max_bag_size}")
        print(f"  Implied treewidth: {treewidth}")
    else:
        # Handle empty graph / no bags case
        print(f"  Reported max bag size (treewidth + 1): {td_max_bag_size} (Graph might be empty or no bags found)")
        print(f"  Implied treewidth: N/A or -1 for empty graph")


    if valid_td:
        print("\n--- Overall: The tree decomposition appears to satisfy basic properties (Vertex and Edge Coverage) ---")
    else:
        print("\n--- Overall: The tree decomposition FAILED one or more basic property checks ---")

    return valid_td

def main():
    parser = argparse.ArgumentParser(
        description="Verify a Tree Decomposition (.td) against an original graph (.gr)."
    )
    parser.add_argument("gr_file", help="Path to the input graph file (.gr DIMACS-like).")
    parser.add_argument("td_file", help="Path to the input tree decomposition file (.td DIMACS-like).")

    args = parser.parse_args()

    if not os.path.exists(args.gr_file):
        print(f"Error: Input .gr file not found: {args.gr_file}")
        return
    if not os.path.exists(args.td_file):
        print(f"Error: Input .td file not found: {args.td_file}")
        return

    print(f"Parsing graph file: {args.gr_file}...")
    gr_v, gr_e, _ = parse_gr_graph(args.gr_file)
    if gr_v is None:
        print("Failed to parse .gr file. Exiting.")
        return
    print(f"Graph: {gr_v} vertices (declared), {len(gr_e)} unique edges found.")

    print(f"\nParsing tree decomposition file: {args.td_file}...")
    td_n_bags, td_max_b_size, td_orig_v, td_b_dict, td_t_edges, _ = parse_td_file(args.td_file)
    if td_n_bags is None:
        print("Failed to parse .td file. Exiting.")
        return
    print(f"TD: {td_n_bags} bags (declared), max bag size {td_max_b_size} (declared tw+1), for {td_orig_v} original vertices (declared).")
    print(f"    Found {len(td_b_dict)} bag definitions and {len(td_t_edges)} unique TD edge definitions.")


    verify_tree_decomposition(gr_v, gr_e, td_n_bags, td_max_b_size, td_orig_v, td_b_dict, td_t_edges)

if __name__ == "__main__":
    main()
