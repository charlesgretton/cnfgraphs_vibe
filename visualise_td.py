## Author -- Gemini 2.5 Pro Preview 05-06

import argparse
import os
import networkx as nx
import matplotlib.pyplot as plt
import graphviz # The Python wrapper for Graphviz
import time

# --- Parser for Matplotlib (needs bag content, even if simplified viz doesn't use it all) ---
def parse_td_file_for_matplotlib_viz(td_filepath):
    """
    Parses a tree decomposition file.
    Returns:
        tuple: (dict_of_bags, list_of_td_edges) or (None, None) on error.
        dict_of_bags: {bag_id_int: set_of_vertices_in_bag_int}
        list_of_td_edges: list of tuples (bag_id1_int, bag_id2_int)
    """
    bags = {} # bag_id (int) -> set of vertex_ids (int)
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
                elif line.startswith('b'): 
                    if not parsed_solution_line:
                         pass # Allow 'b' lines even if 's td' is missing
                    if len(parts) < 2:
                        continue
                    try:
                        bag_id = int(parts[1]) # Store bag_id as int for NetworkX nodes
                        vertex_parts = parts[2:]
                        if vertex_parts and vertex_parts[-1] == '0':
                            vertex_parts = vertex_parts[:-1]
                        
                        bag_vertices = {int(v) for v in vertex_parts} # Vertices as int
                        bags[bag_id] = bag_vertices
                    except ValueError:
                        continue
                elif parsed_solution_line or bags: 
                    edge_node_parts = parts
                    if edge_node_parts and edge_node_parts[-1] == '0':
                        edge_node_parts = edge_node_parts[:-1]
                    
                    if len(edge_node_parts) != 2:
                        continue
                    try:
                        u_bag = int(edge_node_parts[0]) # Bag IDs as int
                        v_bag = int(edge_node_parts[1])
                        td_edges.append(tuple(sorted((u_bag, v_bag))))
                    except ValueError:
                        continue
        
        td_edges = sorted(list(set(td_edges))) 
        if not bags and not td_edges:
            # print(f"Warning: No bags or TD edges found in {td_filepath}.")
            return None, None
        return bags, td_edges
    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None
    except Exception as e:
        print(f"An unexpected error occurred during .td parsing for Matplotlib: {e}")
        return None, None

# --- Parser for Graphviz (needs bag IDs as strings) ---
def parse_td_for_graphviz(td_filepath):
    """
    Parses TD file, returning bag_ids (as strings) and td_edges (strings).
    """
    bag_ids_from_b_lines = set() # Bag IDs defined in 'b' lines
    all_bag_ids_in_edges = set() # All bag IDs appearing in edges
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
                elif line.startswith('b'):
                    if len(parts) >= 2:
                        try:
                            bag_ids_from_b_lines.add(parts[1]) # Store bag_id as string
                        except: pass 
                elif parsed_solution_line or bag_ids_from_b_lines or td_edges: # Check td_edges too for files with only edges
                    edge_node_parts = parts
                    if edge_node_parts and edge_node_parts[-1] == '0':
                        edge_node_parts = edge_node_parts[:-1]
                    if len(edge_node_parts) == 2:
                        try:
                            u_str, v_str = edge_node_parts[0], edge_node_parts[1]
                            td_edges.append((u_str, v_str))
                            all_bag_ids_in_edges.add(u_str)
                            all_bag_ids_in_edges.add(v_str)
                        except: pass 
        
        # Combine all known bag IDs
        final_bag_ids = list(bag_ids_from_b_lines.union(all_bag_ids_in_edges))
        # Graphviz doesn't care about edge order for unique edges, but good practice
        unique_td_edges = sorted(list(set(td_edges)))


        if not final_bag_ids and not unique_td_edges: return None, None
        return final_bag_ids, unique_td_edges
    except FileNotFoundError:
        print(f"Error: Tree decomposition file not found: {td_filepath}")
        return None, None
    except Exception as e:
        print(f"An unexpected error occurred during .td parsing for Graphviz: {e}")
        return None, None

# --- Matplotlib visualization function (visualize_td_shape_matplotlib - assumed to be defined as before) ---
def visualize_td_shape_matplotlib(bags, td_edges, output_filepath="td_shape.png", show_plot=True):
    """
    Visualizes the SHAPE of the tree decomposition quickly using Matplotlib.
    Labels are minimal (just bag IDs).
    `bags` is expected to be a dict {bag_id_int: set_of_vertex_ids_int}
    `td_edges` is expected to be a list of (bag_id_int, bag_id_int)
    """
    if not bags: # Check if bags dict is empty or None
        print("No bags data to visualize for Matplotlib.")
        # Even if td_edges exist, without bag definitions, it's hard to know all nodes
        # unless we infer them solely from edges.
        # For simplicity, require bags to be defined.
        # If td_edges exist but bags is empty, G_td.nodes() might be empty.
        # We can try to build nodes just from edges if bags is empty.
        if not td_edges:
            print("No bags or TD edges to visualize.")
            return
        else: # Only edges given, bags is empty/None
            print("Warning: No 'b' lines found or bags data is empty. Visualizing nodes inferred from edges only.")
            all_nodes_from_edges = set()
            for u,v in td_edges:
                all_nodes_from_edges.add(u)
                all_nodes_from_edges.add(v)
            if not all_nodes_from_edges:
                print("No nodes could be inferred from edges either.")
                return
            # Create dummy bags for NetworkX
            bags = {node_id: set() for node_id in all_nodes_from_edges}


    G_td = nx.Graph()
    
    # Add nodes (bags)
    for bag_id_int in bags.keys(): 
        G_td.add_node(bag_id_int) # NetworkX nodes can be integers

    # Add edges between bags
    for u_int, v_int in td_edges:
        if u_int not in G_td: G_td.add_node(u_int) 
        if v_int not in G_td: G_td.add_node(v_int)
        G_td.add_edge(u_int, v_int)

    if not G_td.nodes():
        print("Graph for Matplotlib TD is empty after processing bags and edges.")
        return

    plt.figure(figsize=(12, 9)) 

    pos = None
    layout_algo = "spring" 
    try:
        print("Attempting to use graphviz_layout (prog='dot') for Matplotlib positioning...")
        start_layout_time = time.time()
        pos = nx.nx_agraph.graphviz_layout(G_td, prog='dot')
        layout_algo = "graphviz_dot"
        print(f"Graphviz layout took {time.time() - start_layout_time:.2f} seconds.")
    except Exception: 
        print("Graphviz layout failed or not available for Matplotlib. Falling back to spring_layout.")
        start_layout_time = time.time()
        pos = nx.spring_layout(G_td, iterations=15, seed=42) 
        print(f"Spring layout took {time.time() - start_layout_time:.2f} seconds.")

    print("Drawing nodes for Matplotlib...")
    start_draw_time = time.time()
    nx.draw_networkx_nodes(G_td, pos, node_size=50, node_color='skyblue', alpha=0.8) 
    print(f"Node drawing took {time.time() - start_draw_time:.2f} seconds.")

    print("Drawing edges for Matplotlib...")
    start_draw_time = time.time()
    nx.draw_networkx_edges(G_td, pos, width=1.0, alpha=0.5, edge_color='gray')
    print(f"Edge drawing took {time.time() - start_draw_time:.2f} seconds.")

    show_labels = False 
    if len(G_td.nodes()) < 500: 
        show_labels = True

    if show_labels:
        print("Drawing labels for Matplotlib...")
        start_draw_time = time.time()
        simple_labels = {node: str(node) for node in G_td.nodes()}
        nx.draw_networkx_labels(G_td, pos, labels=simple_labels, font_size=6, font_color='black')
        print(f"Label drawing took {time.time() - start_draw_time:.2f} seconds.")

    plt.title(f"Tree Decomposition Shape (Matplotlib - {len(G_td.nodes())} bags, {len(G_td.edges())} TD edges, Layout: {layout_algo})", fontsize=14)
    plt.axis('off')

    if output_filepath:
        try:
            print(f"Saving Matplotlib visualization to {output_filepath}...")
            start_save_time = time.time()
            plt.savefig(output_filepath, bbox_inches='tight', dpi=100) 
            print(f"Saving took {time.time() - start_save_time:.2f} seconds.")
        except Exception as e:
            print(f"Error saving Matplotlib visualization to {output_filepath}: {e}")
    
    if show_plot:
        plt.show()
    plt.close()


# --- Graphviz visualization function (visualize_td_shape_graphviz - assumed to be defined as before) ---
def visualize_td_shape_graphviz(bag_node_ids_str_list, td_edges_str_list, output_filepath_base="td_shape_gv", engine='dot', show_details=False):
    """
    Visualizes TD shape using the graphviz library.
    `bag_node_ids_str_list` is a list of bag IDs as strings.
    `td_edges_str_list` is a list of (str, str) tuples for edges.
    """
    if not bag_node_ids_str_list: # Even if edges exist, good to have node list
        print("No bag nodes list to visualize for Graphviz.")
        if not td_edges_str_list:
            print("No bag nodes or TD edges.")
            return
        else: # Infer nodes from edges if bag_node_ids_str_list is empty
            print("Warning: Bag node list is empty, inferring nodes from edges for Graphviz.")
            all_nodes_from_edges = set()
            for u,v in td_edges_str_list:
                all_nodes_from_edges.add(u)
                all_nodes_from_edges.add(v)
            bag_node_ids_str_list = list(all_nodes_from_edges)
            if not bag_node_ids_str_list:
                print("No nodes could be inferred from edges for Graphviz either.")
                return


    dot = graphviz.Graph(comment='Tree Decomposition Shape', engine=engine)
    dot.attr(splines='true') 
    dot.attr(overlap='false') 

    dot.node_attr.update(shape='point', width='0.1', height='0.1', fixedsize='true', color='skyblue', style='filled')
    dot.edge_attr.update(color='gray', penwidth='0.5')

    for node_id_str in bag_node_ids_str_list:
        dot.node(node_id_str, label='' if not show_details else node_id_str) 

    for u_str, v_str in td_edges_str_list:
        dot.edge(u_str, v_str)

    output_format = os.path.splitext(output_filepath_base)[1][1:] or 'png'
    output_filename = os.path.splitext(output_filepath_base)[0]
    
    try:
        print(f"Rendering with Graphviz (engine={engine}) to {output_filename}.{output_format}...")
        start_render_time = time.time()
        rendered_file = dot.render(filename=output_filename, format=output_format, cleanup=True, quiet=True)
        print(f"Graphviz rendering took {time.time() - start_render_time:.2f} seconds.")
        print(f"Visualization saved to {rendered_file}")
    except graphviz.backend.execute.CalledProcessError as e:
        print(f"Error during Graphviz rendering: {e}")
        print("Please ensure Graphviz executables (like 'dot') are installed and in your system's PATH.")
    except Exception as e:
        print(f"An unexpected error occurred with Graphviz: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Visualize the SHAPE of a Tree Decomposition (.td) file."
    )
    parser.add_argument("td_file", help="Path to the input tree decomposition file (.td).")
    parser.add_argument(
        "-o", "--output",
        default="td_shape_visualization", 
        help="Base path for the output image file (e.g., td_shape.png, td_shape.pdf). Default: td_shape_visualization"
    )
    parser.add_argument(
        "--method",
        choices=["matplotlib", "graphviz"],
        default="graphviz",
        help="Visualization method to use (default: graphviz, faster for large graphs)."
    )
    parser.add_argument(
        "--engine",
        default="dot",
        help="Graphviz layout engine to use (e.g., dot, neato, fdp, sfdp, twopi, circo). Default: dot."
    )
    parser.add_argument(
        "--no-show-mpl", 
        action="store_true",
        help="For matplotlib method: Do not display the plot interactively (only save)."
    )
    parser.add_argument(
        "--show-labels-gv", 
        action="store_true",
        help="For graphviz method: Show bag ID labels (can be slow for very many nodes)."
    )

    args = parser.parse_args()

    if not os.path.exists(args.td_file):
        print(f"Error: Input .td file not found: {args.td_file}")
        return

    print(f"Parsing tree decomposition file: {args.td_file} for {args.method} visualization...")
    
    start_parse_time = time.time()
    if args.method == "matplotlib":
        # Use the parser designed for Matplotlib's needs
        bags_data, td_edges_data = parse_td_file_for_matplotlib_viz(args.td_file)
        print(f"Parsing took {time.time() - start_parse_time:.2f} seconds.")
        if bags_data is None and td_edges_data is None : # Check if parsing failed completely
            print("Failed to parse .td file or file was empty. Cannot visualize with Matplotlib.")
            return
        # If bags_data is None but td_edges_data exists, visualize_td_shape_matplotlib will handle it.
        # Similarly if td_edges_data is None but bags_data exists (isolated bags).
        
        # Ensure output has a common image extension if not specified
        output_file_mpl = args.output
        if not any(output_file_mpl.endswith(ext) for ext in ['.png', '.pdf', '.svg']):
            output_file_mpl += ".png"

        visualize_td_shape_matplotlib(bags_data, td_edges_data, output_file_mpl, show_plot=not args.no_show_mpl)
    
    elif args.method == "graphviz":
        # Use the parser designed for Graphviz's needs (string IDs)
        bag_ids_str_list, td_edges_str_list = parse_td_for_graphviz(args.td_file)
        print(f"Parsing took {time.time() - start_parse_time:.2f} seconds.")
        if bag_ids_str_list is None and td_edges_str_list is None:
            print("Failed to parse .td file or file was empty. Cannot visualize with Graphviz.")
            return
        
        output_base_gv = args.output # Graphviz render handles adding extension based on format
        visualize_td_shape_graphviz(bag_ids_str_list, td_edges_str_list, output_base_gv, engine=args.engine, show_details=args.show_labels_gv)

if __name__ == "__main__":
    main()
