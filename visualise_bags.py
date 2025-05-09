## Author -- Gemini 2.5 Pro Preview 05-06

import argparse
import os
import networkx as nx
import matplotlib.pyplot as plt

# --- Re-using and slightly adapting the TD parser ---
def parse_td_file_for_viz(td_filepath):
    """
    Parses a tree decomposition file in .td DIMACS-like format for visualization.
    Returns:
        tuple: (dict_of_bags, list_of_td_edges) or (None, None) on error.
        dict_of_bags: {bag_id: set_of_vertices_in_bag}
        list_of_td_edges: list of tuples (bag_id1, bag_id2)
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
                    if len(parts) != 5: # s td num_bags max_bag_size num_orig_verts
                        print(f"Warning: Malformed 's td' line in {td_filepath} (line {line_num}). Parsing will continue.")
                    # We don't strictly need the 's td' values for visualization itself
                    parsed_solution_line = True
                elif line.startswith('b'): # Bag definition: b <id> v1 v2 ... vn [0]
                    if not parsed_solution_line:
                         print(f"Warning: Bag line 'b' found before 's td' line in {td_filepath} (line {line_num}).")
                    if len(parts) < 2:
                        print(f"Warning: Malformed bag line (too short) in {td_filepath} (line {line_num}). Skipping.")
                        continue
                    try:
                        bag_id = int(parts[1])
                        vertex_parts = parts[2:]
                        if vertex_parts and vertex_parts[-1] == '0':
                            vertex_parts = vertex_parts[:-1]
                        
                        bag_vertices = {int(v) for v in vertex_parts}
                        if bag_id in bags: # Should ideally not happen in valid TD files
                            print(f"Warning: Duplicate bag ID {bag_id} found in {td_filepath} (line {line_num}). Overwriting.")
                        bags[bag_id] = bag_vertices
                    except ValueError:
                        print(f"Warning: Non-integer value in bag line in {td_filepath} (line {line_num}). Skipping.")
                        continue
                elif parsed_solution_line: # TD Edge definition: <bag_id1> <bag_id2> [0]
                    edge_node_parts = parts
                    if edge_node_parts and edge_node_parts[-1] == '0':
                        edge_node_parts = edge_node_parts[:-1]
                    
                    if len(edge_node_parts) != 2:
                         print(f"Warning: Malformed TD edge line (expected 2 bag IDs) in {td_filepath} (line {line_num}). Skipping.")
                         continue
                    try:
                        u_bag, v_bag = int(edge_node_parts[0]), int(edge_node_parts[1])
                        td_edges.append(tuple(sorted((u_bag, v_bag))))
                    except ValueError:
                        print(f"Warning: Non-integer bag ID in TD edge line in {td_filepath} (line {line_num}). Skipping.")
                        continue
                # else: (line before 's td' that is not 'c' or 'b')
                #    print(f"Warning: Unexpected line before 's td' in {td_filepath} (line {line_num}). Skipping.")


        # Remove duplicate TD edges
        td_edges = sorted(list(set(td_edges)))
        
        if not bags and not td_edges:
            print(f"Warning: No bags or TD edges found in {td_filepath}. Is the file empty or only comments?")
            return None, None
            
        return bags, td_edges

    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None
    except Exception as e:
        print(f"An unexpected error occurred during .td parsing: {e}")
        return None, None

def visualize_tree_decomposition_matplotlib(bags, td_edges, output_filepath="td_visualization.png", show_plot=True):
    """
    Visualizes the tree decomposition using NetworkX and Matplotlib.
    """
    if not bags:
        print("No bags to visualize.")
        return

    G_td = nx.Graph()
    node_labels = {}

    max_bag_content_display = 10 # Max number of vertex IDs to show in label to avoid clutter

    for bag_id, vertices in bags.items():
        G_td.add_node(bag_id)
        # Create a readable label for the bag
        if vertices:
            sorted_vertices = sorted(list(vertices))
            if len(sorted_vertices) > max_bag_content_display:
                label_content = ", ".join(map(str, sorted_vertices[:max_bag_content_display])) + ", ..."
            else:
                label_content = ", ".join(map(str, sorted_vertices))
            node_labels[bag_id] = f"B{bag_id}\n{{{label_content}}}\n(Size: {len(vertices)})"
        else:
            node_labels[bag_id] = f"B{bag_id}\n{{}}\n(Size: 0)"


    for u, v in td_edges:
        if u not in G_td or v not in G_td:
            print(f"Warning: TD edge ({u},{v}) references a bag not defined. Skipping this edge in visualization.")
            continue
        G_td.add_edge(u, v)

    if not G_td.nodes():
        print("Graph for TD is empty after processing bags and edges.")
        return

    plt.figure(figsize=(16, 12)) # Adjust figure size as needed

    # Try to use a layout suitable for trees if pygraphviz is available
    pos = None
    try:
        # `nx.nx_agraph.graphviz_layout` requires pygraphviz and Graphviz installed
        pos = nx.nx_agraph.graphviz_layout(G_td, prog='dot') # 'dot' is good for hierarchical/tree layouts
        print("Using graphviz_layout (prog='dot') for positioning.")
    except ImportError:
        print("pygraphviz not found. Falling back to spring_layout for node positioning.")
        print("For better tree layouts, consider installing pygraphviz and Graphviz.")
        pos = nx.spring_layout(G_td, k=1.5/max(1, (len(G_td.nodes())**0.5)), iterations=50, seed=42)
    except Exception as e: # Catch other errors from graphviz_layout (e.g., Graphviz not in PATH)
        print(f"Graphviz layout failed: {e}. Falling back to spring_layout.")
        pos = nx.spring_layout(G_td, k=1.5/max(1, (len(G_td.nodes())**0.5)), iterations=50, seed=42)


    # Node sizes can be varied, e.g., by bag size, but keep it simple for now
    node_sizes = [len(bags.get(node, [])) * 100 + 500 for node in G_td.nodes()] # Basic sizing based on bag content size
    min_node_size = 500
    node_sizes = [max(s, min_node_size) for s in node_sizes]


    nx.draw_networkx_nodes(G_td, pos, node_size=node_sizes, node_color='skyblue', alpha=0.9)
    nx.draw_networkx_edges(G_td, pos, width=1.5, alpha=0.7, edge_color='gray')
    nx.draw_networkx_labels(G_td, pos, labels=node_labels, font_size=8, font_weight='bold')

    plt.title(f"Tree Decomposition Visualization ({len(G_td.nodes())} bags, {len(G_td.edges())} TD edges)", fontsize=16)
    plt.axis('off')  # Turn off the axis

    if output_filepath:
        try:
            plt.savefig(output_filepath, bbox_inches='tight', dpi=150)
            print(f"Visualization saved to {output_filepath}")
        except Exception as e:
            print(f"Error saving visualization to {output_filepath}: {e}")
    
    if show_plot:
        plt.show()
    plt.close() # Close the figure to free memory

def main():
    parser = argparse.ArgumentParser(
        description="Visualize a Tree Decomposition (.td) file graphically."
    )
    parser.add_argument("td_file", help="Path to the input tree decomposition file (.td DIMACS-like).")
    parser.add_argument(
        "-o", "--output", 
        default="td_visualization.png",
        help="Path to save the output image file (e.g., td.png, td.pdf). Default: td_visualization.png"
    )
    parser.add_argument(
        "--no-show",
        action="store_true",
        help="Do not display the plot interactively (only save to file if -o is specified)."
    )

    args = parser.parse_args()

    if not os.path.exists(args.td_file):
        print(f"Error: Input .td file not found: {args.td_file}")
        return

    print(f"Parsing tree decomposition file: {args.td_file}...")
    bags_data, td_edges_data = parse_td_file_for_viz(args.td_file)

    if bags_data is None:
        print("Failed to parse .td file or file was empty. Cannot visualize.")
        return
    
    print(f"Found {len(bags_data)} bags and {len(td_edges_data)} TD edges.")
    
    visualize_tree_decomposition_matplotlib(
        bags_data, 
        td_edges_data, 
        output_filepath=args.output,
        show_plot=not args.no_show
    )

if __name__ == "__main__":
    main()
