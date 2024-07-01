def read_hex_file(file_path):
    """Reads a file and returns a list of numbers converted from hex to decimal."""
    with open(file_path, 'r') as file:
        lines = file.readlines()
    hex_numbers = []
    for line in lines:
        try:
            hex_numbers.append(int(line.strip(), 16))
        except ValueError:
            print(f"Skipping invalid hexadecimal number: {line.strip()}")
    return hex_numbers

def read_dec_file(file_path):
    """Reads a file and returns a list of decimal numbers."""
    with open(file_path, 'r') as file:
        lines = file.readlines()
    dec_numbers = []
    for line in lines:
        try:
            dec_numbers.append(float(line.strip()))
        except ValueError:
            print(f"Skipping invalid decimal number: {line.strip()}")
    return dec_numbers

def compare_files(hex_file_path, dec_file_path):
    """Compares two files (hex and decimal) and returns a report of differences."""
    hex_lines = read_hex_file(hex_file_path)
    dec_lines = read_dec_file(dec_file_path)
    
    max_len = max(len(hex_lines), len(dec_lines))
    report = []

    for i in range(max_len):
        hex_value = hex_lines[i] if i < len(hex_lines) else None
        dec_value = dec_lines[i] if i < len(dec_lines) else None
        
        if hex_value is not None and dec_value is not None:
            difference = hex_value - dec_value
        else:
            difference = None

        report.append({
            'line': i + 1,
            'hex_value': hex_value,
            'dec_value': dec_value,
            'difference': difference
        })
    
    return report

def generate_html_report(report, output_path, custom_content=""):
    """Generates a detailed comparison report in HTML format and saves it to a file."""
    title = "Comparison Report"
    if custom_content:
        title += f" {custom_content}"

    html_content = f"""
    <html>
    <head>
        <title>{title}</title>
        <style>
            table {{
                width: 100%;
                border-collapse: collapse;
            }}
            th, td {{
                border: 1px solid black;
                padding: 8px;
                text-align: center;
            }}
            th {{
                background-color: #f2f2f2;
            }}
        </style>
    </head>
    <body>
        <h2>{title}</h2>
        <table>
            <tr>
                <th>Line</th>
                <th>Hex Value</th>
                <th>Decimal Value</th>
                <th>Difference</th>
            </tr>
    """
    for entry in report:
        line = entry['line']
        hex_value = entry['hex_value']
        dec_value = entry['dec_value']
        difference = entry['difference']
        html_content += f"""
            <tr>
                <td>{line}</td>
                <td>{hex_value}</td>
                <td>{dec_value}</td>
                <td>{difference}</td>
            </tr>
        """
    html_content += """
        </table>
    </body>
    </html>
    """
    
    with open(output_path, 'w') as file:
        file.write(html_content)


for i in range(24):    
    # File paths
    hex_file_path = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/conv1_real_results/DUT_out_channel_{i}.txt'
    dec_file_path = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/conv1_expected_results/Expected_out_channel_{i}.txt'
    output_path   = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/result_compare/comparison_report_{i}.html'
    
    # Perform comparison and generate HTML report
    report = compare_files(hex_file_path, dec_file_path)
    generate_html_report(report, output_path, f'Channel {i}')
    
    print(f"Comparison report generated: {output_path}")



