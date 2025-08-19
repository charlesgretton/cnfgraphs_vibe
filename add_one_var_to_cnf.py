import argparse

def process_cnf(input_cnf_filepath, output_cnf_filepath):
    """
    Parses an input CNF file, removes comments, adds one new variable,
    and adds a new clause asserting this new variable is true.

    Args:
        input_cnf_filepath (str): Path to the input DIMACS CNF file.
        output_cnf_filepath (str): Path for the modified output DIMACS CNF file.
    """
    original_clauses_lines = []
    num_original_vars = 0
    num_original_clauses = 0
    found_p_line = False

    # --- First Pass: Read existing CNF and extract info ---
    with open(input_cnf_filepath, 'r') as infile:
        for line in infile:
            line = line.strip()
            if not line:  # Skip empty lines
                continue
            if line.startswith('c'):  # Skip comment lines
                continue
            if line.startswith('p cnf'):
                if found_p_line:
                    print("Warning: Multiple 'p cnf' lines found. Using the first one.")
                    original_clauses_lines.append(line) # Keep it as a clause if it's extra
                    continue
                try:
                    parts = line.split()
                    num_original_vars = int(parts[2])
                    num_original_clauses = int(parts[3])
                    found_p_line = True
                except (IndexError, ValueError):
                    raise ValueError(f"Malformed 'p cnf' line: {line}")
            else:
                # Assume it's a clause line
                original_clauses_lines.append(line)

    if not found_p_line:
        raise ValueError("Input CNF file does not contain a 'p cnf' line.")

    # Validate actual clause count against declared (optional, but good practice)
    if len(original_clauses_lines) != num_original_clauses:
        print(f"Warning: Declared clauses ({num_original_clauses}) "
              f"does not match found clauses ({len(original_clauses_lines)}). "
              f"Using found clause count for output.")
        num_original_clauses = len(original_clauses_lines)


    # --- Second Pass: Write the modified CNF ---
    new_num_vars = num_original_vars + 1
    new_num_clauses = num_original_clauses + 1
    new_variable_id = new_num_vars # The new variable will have the highest ID

    with open(output_cnf_filepath, 'w') as outfile:
        # Write the new problem line
        outfile.write(f"p cnf {new_num_vars} {new_num_clauses}\n")

        # Write all original (non-comment) clauses
        for clause_line in original_clauses_lines:
            outfile.write(f"{clause_line}\n")

        # Add the new clause asserting the new variable is true
        # The clause is just "(new_variable_id)"
        outfile.write(f"{new_variable_id} 0\n")

    print(f"Processed CNF file: {input_cnf_filepath}")
    print(f"  Original vars: {num_original_vars}, Original clauses: {len(original_clauses_lines)}")
    print(f"  New vars: {new_num_vars}, New clauses: {new_num_clauses}")
    print(f"  New variable {new_variable_id} added and asserted true.")
    print(f"Modified CNF written to: {output_cnf_filepath}")


def main():
    parser = argparse.ArgumentParser(
        description="Modifies a DIMACS CNF file: removes comments, adds a new variable, "
                    "and adds a clause asserting the new variable is true."
    )
    parser.add_argument("input_cnf", help="Path to the input DIMACS CNF file.")
    parser.add_argument("output_cnf", help="Path for the modified output DIMACS CNF file.")

    args = parser.parse_args()

    try:
        process_cnf(args.input_cnf, args.output_cnf)
    except FileNotFoundError:
        print(f"Error: Input file '{args.input_cnf}' not found.")
    except ValueError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()