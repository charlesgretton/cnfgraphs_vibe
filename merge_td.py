import argparse
import sys

def parse_td_file(filepath):
    """
    Parses a .td file.
    Returns:
        bags (dict): {bag_id: set_of_vertices}
        adj (dict): {bag_id: set_of_adjacent_bag_ids}
        original_num_bags (int)
        treewidth_plus_1 (int)
        num_original_vertices (int)
    """
    bags = {}
    adj = {}
    original_num_bags = 0
    treewidth_plus_1 = 0
    num_original_vertices = 0
    parsing_edges = False

    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue

            parts = line.split()
            if parts[0] == 's':
                # s td <num_bags> <treewidth+1> <num_original_vertices>
                original_num_bags = int(parts[2])
                treewidth_plus_1 = int(parts[3])
                num_original_vertices = int(parts[4])
                parsing_edges = False # Reset in case of multiple 's' lines (though unlikely)
            elif parts[0] == 'b':
                # b <bag_id> <vertex1> <vertex2> ...
                bag_id = int(parts[1])
                bag_content = {int(v) for v in parts[2:]}
                bags[bag_id] = bag_content
                if bag_id not in adj: # Initialize adjacency list for this bag
                    adj[bag_id] = set()
                parsing_edges = False
            else:
                # Edge between bags: <adj_bag_id_1> <adj_bag_id_2>
                # Can also be part of the 's' line if it's the start of edges.
                # Heuristic: if not 's' or 'b', assume it's an edge line.
                # A more robust parser might check if parsing_edges was set after 's'
                # if the 's' line itself implied the end of bag definitions.
                # For now, this handles common .td structures.
                try:
                    u, v = int(parts[0]), int(parts[1])
                    if u not in adj: adj[u] = set()
                    if v not in adj: adj[v] = set()
                    adj[u].add(v)
                    adj[v].add(u)
                    parsing_edges = True # Confirms we are in the edge section
                except ValueError:
                    print(f"Warning: Skipping malformed line: {line}", file=sys.stderr)
                    continue
    return bags, adj, original_num_bags, treewidth_plus_1, num_original_vertices

def merge_two_bags(bags, adj, b_remove, b_keep):
    """
    Merges bag b_remove into b_keep.
    - b_keep's content becomes union of b_keep and b_remove.
    - Neighbors of b_remove (excluding b_keep) become neighbors of b_keep.
    - b_remove is deleted from bags and adj.
    """
    if b_remove not in bags or b_keep not in bags:
        print(f"Error: Bag {b_remove} or {b_keep} not found for merging.", file=sys.stderr)
        return False

    # print(f"  Merging bag {b_remove} ({bags[b_remove]}) into bag {b_keep} ({bags[b_keep]})")

    # Update content of b_keep
    bags[b_keep].update(bags[b_remove])

    # Rewire neighbors
    neighbors_of_b_remove = list(adj.get(b_remove, [])) # list to avoid issues if b_remove is in its own adj (should not happen)

    for neighbor in neighbors_of_b_remove:
        if neighbor != b_keep: # Don't add b_keep to its own adjacency or process itself
            if neighbor in adj: # Neighbor might have been removed in a previous step
                adj[neighbor].add(b_keep)
                adj[neighbor].discard(b_remove) # Remove old link
            if b_keep in adj: # b_keep should exist
                 adj[b_keep].add(neighbor)
        elif neighbor == b_keep: # if b_remove was adjacent to b_keep
            if b_keep in adj:
                 adj[b_keep].discard(b_remove) # remove direct link from b_keep to b_remove


    # Delete b_remove
    del bags[b_remove]
    if b_remove in adj:
        # Also remove b_remove from all other adjacency lists
        for b_id in list(adj.keys()): # Iterate over copy of keys
            if b_id in adj and b_remove in adj[b_id]:
                adj[b_id].discard(b_remove)
        del adj[b_remove]
    
    # Ensure b_keep does not list itself as adjacent
    if b_keep in adj and b_keep in adj[b_keep]:
        adj[b_keep].discard(b_keep)

    # print(f"  Result: bag {b_keep} is now {bags[b_keep]}, adj: {adj.get(b_keep)}")
    return True


def normalize_decomposition(bags, adj):
    """
    Iteratively merges bags where one is a subset of an adjacent bag.
    This is width-preserving.
    Returns True if any merge happened, False otherwise.
    """
    made_change_in_pass = True
    any_change_overall = False

    while made_change_in_pass:
        made_change_in_pass = False
        # Iterate over a copy of bag IDs as keys might change
        # And over copy of edges as adj structure changes
        
        edges_to_check = []
        for u in list(bags.keys()):
            if u not in adj: continue
            for v in list(adj[u]): # Iterate over copy of neighbors
                 if u < v: # Process each edge once
                    edges_to_check.append((u,v))
        
        if not edges_to_check and len(bags) > 1:
             # This can happen if the graph becomes disconnected during merges
             # Or if there's an issue with adj updates.
             pass # Continue to see if we can break the loop later


        for u, v in edges_to_check:
            if u not in bags or v not in bags: # One might have been merged already
                continue

            bag_u_content = bags[u]
            bag_v_content = bags[v]

            merged = False
            if bag_u_content.issubset(bag_v_content) and bag_u_content != bag_v_content:
                print(f"Normalization: Bag {u} {bag_u_content} is subset of Bag {v} {bag_v_content}. Merging {u} into {v}.")
                merge_two_bags(bags, adj, u, v)
                merged = True
            elif bag_v_content.issubset(bag_u_content) and bag_v_content != bag_u_content:
                print(f"Normalization: Bag {v} {bag_v_content} is subset of Bag {u} {bag_u_content}. Merging {v} into {u}.")
                merge_two_bags(bags, adj, v, u)
                merged = True
            
            if merged:
                made_change_in_pass = True
                any_change_overall = True
                break # Restart search from the beginning as structure changed

        if not made_change_in_pass and not edges_to_check and len(bags) > 1 :
            # If no edges to check but multiple bags, it means graph is disconnected.
            # Normalization within components is done.
            break


    return any_change_overall


def aggressively_merge_to_target(bags, adj, target_bag_count):
    """
    Aggressively merges bags until target_bag_count is reached.
    Strategy: merge adjacent bags (u,v) such that len(bag(u) U bag(v)) is minimized.
    """
    if len(bags) <= target_bag_count:
        return

    print(f"\nStarting aggressive merging. Current bags: {len(bags)}, Target: {target_bag_count}")

    while len(bags) > target_bag_count and len(bags) > 1:
        best_edge_to_merge = None
        min_resulting_bag_size = float('inf')
        # Bag ID to remove, Bag ID to keep (merge into)
        b_remove_candidate, b_keep_candidate = -1, -1

        candidate_edges = []
        for u_node in list(bags.keys()): # Iterate over copy of bag IDs
            if u_node not in adj: continue
            for v_node in list(adj[u_node]): # Iterate over copy of neighbors
                 if u_node < v_node: # Process each edge once
                    candidate_edges.append((u_node, v_node))
        
        if not candidate_edges:
            print("No more edges to merge. Stopping aggressive merge.")
            break

        for u, v in candidate_edges:
            if u not in bags or v not in bags: continue # Should not happen if list is fresh

            resulting_union_size = len(bags[u].union(bags[v]))
            
            if resulting_union_size < min_resulting_bag_size:
                min_resulting_bag_size = resulting_union_size
                # Heuristic: keep the one with larger original ID, or larger bag initially
                # For simplicity, let's say we merge smaller ID into larger ID
                if u < v:
                    b_remove_candidate, b_keep_candidate = u, v
                else:
                    b_remove_candidate, b_keep_candidate = v, u
            # Could add tie-breaking rules here (e.g., prefer merging smaller bags)

        if b_remove_candidate != -1:
            print(f"Aggressive merge: Best choice is merging {b_remove_candidate} into {b_keep_candidate}.")
            print(f"  Bag {b_remove_candidate}: {bags[b_remove_candidate]}, Bag {b_keep_candidate}: {bags[b_keep_candidate]}")
            print(f"  Resulting union size: {min_resulting_bag_size}")
            merge_two_bags(bags, adj, b_remove_candidate, b_keep_candidate)
            print(f"  Bags remaining: {len(bags)}")
        else:
            # This should ideally not be reached if there are bags and edges
            print("Could not find a pair to merge aggressively. Stopping.")
            break
        
        # Sanity check for empty adjacency lists if a bag still exists
        for bag_id_check in list(adj.keys()):
            if bag_id_check in bags and not adj[bag_id_check] and len(bags) > 1:
                # This bag is now isolated. It cannot be merged further unless it's the last one.
                # Or if the target allows multiple components.
                pass


def print_decomposition_state(bags, adj, message="Current Decomposition State"):
    print(f"\n--- {message} ---")
    print(f"Number of bags: {len(bags)}")
    if not bags:
        print("No bags remaining.")
        return
        
    max_bag_size = 0
    for bag_id in sorted(bags.keys()):
        content = sorted(list(bags[bag_id]))
        max_bag_size = max(max_bag_size, len(content))
        adj_list_str = sorted(list(adj.get(bag_id, set())))
        print(f"  Bag {bag_id}: {content} (Size: {len(content)}) --> Neighbors: {adj_list_str}")
    
    if max_bag_size > 0:
        print(f"Current treewidth: {max_bag_size - 1}")
    else:
        print("Current treewidth: N/A (no bags or empty bags)")
    print("--------------------")

def write_td_file(filepath, bags, adj, num_original_vertices_param):
    """Writes the current decomposition to a .td file."""
    if not bags:
        print("Cannot write .td file: No bags in decomposition.", file=sys.stderr)
        return

    num_bags_out = len(bags)
    max_bag_size_out = 0
    for bag_content in bags.values():
        max_bag_size_out = max(max_bag_size_out, len(bag_content))
    
    treewidth_plus_1_out = max_bag_size_out # tw = max_bag_size - 1
    
    # Re-map bag IDs to be sequential 1-based for clean output, if desired
    # For now, use original IDs that remain.
    # If re-mapping:
    # old_to_new_id_map = {old_id: new_id for new_id, old_id in enumerate(sorted(bags.keys()), 1)}
    # new_bags = {old_to_new_id_map[old_id]: content for old_id, content in bags.items()}
    # new_adj = {old_to_new_id_map[old_id]: {old_to_new_id_map[n_old_id] for n_old_id in adj_set}
    #            for old_id, adj_set in adj.items() if old_id in old_to_new_id_map}
    # bags_to_write = new_bags
    # adj_to_write = new_adj

    bags_to_write = bags
    adj_to_write = adj


    with open(filepath, 'w') as f:
        f.write(f"s td {num_bags_out} {treewidth_plus_1_out} {num_original_vertices_param}\n")
        
        # Write bags
        for bag_id in sorted(bags_to_write.keys()):
            content_str = " ".join(map(str, sorted(list(bags_to_write[bag_id]))))
            f.write(f"b {bag_id} {content_str}\n")
            
        # Write edges
        written_edges = set()
        for u in sorted(adj_to_write.keys()):
            if u not in bags_to_write: continue # Skip if bag was removed but adj entry lingered
            for v in sorted(list(adj_to_write[u])):
                if v not in bags_to_write: continue
                # Ensure each edge (u,v) is written once, with smaller ID first
                u_small, v_large = min(u,v), max(u,v)
                if (u_small, v_large) not in written_edges:
                    f.write(f"{u_small} {v_large}\n")
                    written_edges.add((u_small, v_large))
    print(f"\nDecomposition written to {filepath}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Reads a .td file and merges bags to reach a target count.")
    parser.add_argument("td_file", help="Path to the input .td file")
    parser.add_argument("target_bags", type=int, help="Target number of bags for the final decomposition")
    parser.add_argument("--output_file", "-o", help="Path to save the modified .td file (optional)")
    parser.add_argument("--skip_normalization", action="store_true", help="Skip the initial normalization (subset merging) phase.")

    args = parser.parse_args()

    if args.target_bags < 1:
        print("Error: Target bags must be at least 1.", file=sys.stderr)
        sys.exit(1)

    print(f"Reading TD from: {args.td_file}")
    bags_map, adj_map, _, _, num_orig_v = parse_td_file(args.td_file)

    if not bags_map:
        print("Error: No bags parsed from the file.", file=sys.stderr)
        sys.exit(1)

    print_decomposition_state(bags_map, adj_map, "Initial Decomposition")
    
    if not args.skip_normalization:
        print("\nStarting Normalization Phase (merging strict subsets)...")
        normalize_decomposition(bags_map, adj_map)
        print_decomposition_state(bags_map, adj_map, "After Normalization")
    else:
        print("\nSkipping Normalization Phase.")

    if len(bags_map) > args.target_bags:
        aggressively_merge_to_target(bags_map, adj_map, args.target_bags)
        print_decomposition_state(bags_map, adj_map, "After Aggressive Merging")
    else:
        print(f"\nNumber of bags ({len(bags_map)}) is already at or below target ({args.target_bags}). No aggressive merging needed.")

    if args.output_file:
        write_td_file(args.output_file, bags_map, adj_map, num_orig_v)

    print("\nProcessing complete.")