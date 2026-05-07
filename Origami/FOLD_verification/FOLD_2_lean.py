import re

def parse_fold_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()

    extracted_data = {}

    # Extract vertices_coords
    v_match = re.search(r'"vertices_coords":\s*\[(.*?)\]\s*,\s*"', content, re.DOTALL)
    if v_match:
        extracted_data['vertices'] = [
            [float(x) for x in re.findall(r'-?\d+\.?\d*', row)]
            for row in re.findall(r'\[([^\]]+)\]', v_match.group(1))
        ]

    # Extract edges_vertices
    e_match = re.search(r'"edges_vertices":\s*\[(.*?)\]\s*,\s*"', content, re.DOTALL)
    if e_match:
        extracted_data['edges'] = [
            [int(x) for x in re.findall(r'\d+', row)]
            for row in re.findall(r'\[([^\]]+)\]', e_match.group(1))
        ]

    # Extract edges_assignment
    a_match = re.search(r'"edges_assignment":\s*\[(.*?)\]\s*,\s*"', content, re.DOTALL)
    if a_match:
        extracted_data['edges_assignments'] = re.findall(r'"([^"]+)"', a_match.group(1))

    return extracted_data


data = parse_fold_file('data/simple.json')
print(data)