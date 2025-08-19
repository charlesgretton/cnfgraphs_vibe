import argparse
import re
from collections import defaultdict

def parse_cnf(cnf_filepath):
    """
    Parses a DIMACS CNF file to extract all unique variables used.
    """
    used_variables = set()
    max_var_in_cnf = 0
    num_clauses_in_cnf = 0
    declared_vars = 0
    declared_clauses = 0

    with open(cnf_filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p cnf'):
                parts = line.split()
                if len(parts) == 4:
                    declared_vars = int(parts[2])
                    declared_clauses = int(parts[3])
                continue

            # Clause line
            num_clauses_in_cnf += 1
            variables_in_clause = [int(x) for x in line.split()[:-1]] # Exclude trailing 0
            for var_literal in variables_in_clause:
                var = abs(var_literal)
                used_variables.add(var)
                if var > max_var_in_cnf:
                    max_var_in_cnf = var
    
    print(f"CNF Info: Found {len(used_variables)} unique variables (max ID: {max_var_in_cnf}).")
    print(f"CNF Info: Parsed {num_clauses_in_cnf} clauses (declared: {declared_vars} vars, {declared_clauses} clauses).")
    return used_variables, max_var_in_cnf

def parse_td(td_filepath):
    """
    Parses a DIMACS Tree Decomposition file.
    Returns:
        - s_line_params: tuple (num_bags, treewidth_plus_1, num_original_vertices)
        - bags: dict mapping bag_id (int) to a set of variables (int)
        - edges: list of tuples (bag_id1, bag_id2)
        - comments: list of comment lines
    """
    s_line_params = None
    bags = {}
    edges = []
    comments = []

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
                    s_line_params = (int(parts[2]), int(parts[3]), int(parts[4]))
                else:
                    raise ValueError(f"Malformed 's td' line: {line}")
            elif parts[0] == 'b':
                if len(parts) >= 2:
                    bag_id = int(parts[1])
                    bag_vars = {int(v) for v in parts[2:]}
                    bags[bag_id] = bag_vars
                else:
                    raise ValueError(f"Malformed 'b' line: {line}")
            else:
                # Assuming it's an edge line if not 's', 'b', or 'c'
                try:
                    u, v = int(parts[0]), int(parts[1])
                    # Store edges uniquely, typically smaller id first for consistency
                    edges.append(tuple(sorted((u, v))))
                except (ValueError, IndexError):
                    print(f"Warning: Skipping unrecognized line in TD file: {line}")
                    
    if s_line_params is None:
        raise ValueError("TD file does not contain a valid 's td' line.")
    if not bags:
        print("Warning: No bags found in the TD file.")

    # Remove duplicate edges
    edges = sorted(list(set(edges)))
    
    return s_line_params, bags, edges, comments

def clean_tree_decomposition(cnf_used_variables, max_var_in_cnf,
                             td_s_line_params, td_bags, td_edges, td_comments):
    """
    Cleans the tree decomposition by:
    1. Filtering variables in bags based on cnf_used_variables.
    2. Removing empty bags.
    3. Re-indexing bags and edges.
    4. Calculating new treewidth.
    """
    original_num_bags, _, _ = td_s_line_params

    # 1. Filter variables in bags
    filtered_bags_temp = {}
    for bag_id, variables in td_bags.items():
        valid_vars = {var for var in variables if var in cnf_used_variables}
        if valid_vars: # Only keep non-empty bags
            filtered_bags_temp[bag_id] = valid_vars

    if not filtered_bags_temp:
        print("Warning: All bags became empty after filtering. Output will be an empty TD.")
        return ["c Original TD became empty after filtering based on CNF variables"], \
               "s td 0 0 0\n", [], []


    # 2. Re-index remaining bags
    # Sort old bag IDs to make re-indexing deterministic (though not strictly necessary)
    old_ids_sorted = sorted(filtered_bags_temp.keys())
    
    new_bags = {}
    old_to_new_id_map = {}
    new_bag_id_counter = 1
    for old_id in old_ids_sorted:
        old_to_new_id_map[old_id] = new_bag_id_counter
        new_bags[new_bag_id_counter] = filtered_bags_temp[old_id]
        new_bag_id_counter += 1
    
    num_new_bags = len(new_bags)

    # 3. Reconstruct edges using new bag IDs
    new_edges = []
    for u_old, v_old in td_edges:
        # Check if both ends of the original edge correspond to bags that survived filtering
        if u_old in old_to_new_id_map and v_old in old_to_new_id_map:
            u_new = old_to_new_id_map[u_old]
            v_new = old_to_new_id_map[v_old]
            if u_new != v_new: # Avoid self-loops if they somehow arise
                 new_edges.append(tuple(sorted((u_new, v_new))))
    
    new_edges = sorted(list(set(new_edges))) # Ensure uniqueness and order

    # 4. Calculate new treewidth
    new_treewidth = 0
    if new_bags:
        new_treewidth = max(len(bag_vars) for bag_vars in new_bags.values()) -1
    if new_treewidth < 0: # e.g. if all bags have 0 or 1 var
        new_treewidth = 0 


    # Prepare new s-line
    # Use max_var_in_cnf for the number of original vertices,
    # or len(cnf_used_variables) if you prefer the count of unique used vars.
    # Most tools expect the max variable ID as the "number of original vertices".
    num_original_vertices_for_s_line = max_var_in_cnf if cnf_used_variables else 0
    
    new_s_line = f"s td {num_new_bags} {new_treewidth + 1} {num_original_vertices_for_s_line}\n"

    print(f"TD Cleaning: Original bags: {original_num_bags}, New bags: {num_new_bags}")
    print(f"TD Cleaning: New treewidth: {new_treewidth}")

    # Add some comments about the cleaning process
    new_comments = list(td_comments) # Make a copy
    new_comments.append("c Cleaned by script: removed variables not in CNF and empty bags.")
    new_comments.append(f"c Original number of bags: {original_num_bags}")
    new_comments.append(f"c Original treewidth+1: {td_s_line_params[1]}")
    new_comments.append(f"c Original num_vertices: {td_s_line_params[2]}")

    return new_comments, new_s_line, new_bags, new_edges


def write_td(output_filepath, comments, s_line, bags, edges):
    """
    Writes the tree decomposition to a file in DIMACS TD format.
    """
    with open(output_filepath, 'w') as f:
        for comment in comments:
            f.write(f"{comment}\n")
        f.write(s_line)
        
        # Sort bag IDs for deterministic output
        for bag_id in sorted(bags.keys()):
            # Sort variables within the bag for deterministic output
            bag_vars_str = " ".join(map(str, sorted(list(bags[bag_id]))))
            f.write(f"b {bag_id} {bag_vars_str}\n")
            
        for u, v in sorted(edges): # Sort edges for deterministic output
            f.write(f"{u} {v}\n")
    print(f"Cleaned TD written to: {output_filepath}")


def main():
    parser = argparse.ArgumentParser(
        description="Cleans a DIMACS tree decomposition file by removing variables "
                    "not present in a corresponding DIMACS CNF file, and prunes empty bags."
    )
    parser.add_argument("cnf_file", help="Path to the input DIMACS CNF file.")
    parser.add_argument("td_file", help="Path to the input DIMACS TD file.")
    parser.add_argument("output_td_file", help="Path for the cleaned output DIMACS TD file.")
    
    args = parser.parse_args()

    try:
        print(f"Parsing CNF file: {args.cnf_file}")
        cnf_used_vars, max_var_in_cnf = parse_cnf(args.cnf_file)
        if not cnf_used_vars:
            print("Warning: No variables found in the CNF file. The output TD might be empty or strange.")

        print(f"\nParsing TD file: {args.td_file}")
        s_params, bags_orig, edges_orig, comments_orig = parse_td(args.td_file)

        print("\nCleaning tree decomposition...")
        new_comments, new_s_line, new_bags, new_edges = clean_tree_decomposition(
            cnf_used_vars, max_var_in_cnf, s_params, bags_orig, edges_orig, comments_orig
        )
        
        write_td(args.output_td_file, new_comments, new_s_line, new_bags, new_edges)

    except FileNotFoundError as e:
        print(f"Error: File not found - {e.filename}")
    except ValueError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()