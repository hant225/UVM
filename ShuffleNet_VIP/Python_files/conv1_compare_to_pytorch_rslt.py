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
            dec_numbers.append(int(line.strip()))
        except ValueError:
            print(f"Skipping invalid decimal number: {line.strip()}")
    return dec_numbers

def compare_files(hex_file_path, dec_file_path):
    """Compares two files (hex and decimal) and returns a report of differences, including match and mismatch statistics."""
    hex_lines = read_hex_file(hex_file_path)
    dec_lines = read_dec_file(dec_file_path)
    
    max_len = max(len(hex_lines), len(dec_lines))
    report = []

    match_count = 0
    mismatch_count = 0
    total_mismatch_difference = 0

    for i in range(max_len):
        hex_value = hex_lines[i] if i < len(hex_lines) else None
        dec_value = dec_lines[i] if i < len(dec_lines) else None
        
        if hex_value is not None and dec_value is not None:
            difference = hex_value - dec_value
            if hex_value == dec_value:
                match_count += 1
            else:
                mismatch_count += 1
                total_mismatch_difference += abs(difference)
        else:
            difference = None

        report.append({
            'line': i + 1,
            'hex_value': hex_value,
            'dec_value': dec_value,
            'difference': difference
        })

    average_mismatch_difference = (total_mismatch_difference / mismatch_count) if mismatch_count else 0
    
    return report, match_count, mismatch_count, average_mismatch_difference

def generate_html_report(report, match_count, mismatch_count, average_mismatch_difference, output_path, custom_content=""):
    """Generates a detailed comparison report in HTML format and saves it to a file."""
    title = "[CONV1] Comparison Report"
    if custom_content:
        title += f" {custom_content}"

    # Prepare data for the chart
    difference_counts = {}
    for entry in report:
        difference = entry['difference']
        if difference is not None:
            abs_difference = abs(difference)
            if abs_difference in difference_counts:
                difference_counts[abs_difference] += 1
            else:
                difference_counts[abs_difference] = 1

    # Convert counts dictionary to lists and sort by difference values
    sorted_difference_counts = sorted(difference_counts.items())
    difference_values = [item[0] for item in sorted_difference_counts]
    difference_counts_values = [item[1] for item in sorted_difference_counts]

    # Determine colors for each bar based on difference value
    bar_colors = ['rgba(54, 162, 235, 1)' if value != 0 else 'rgba(75, 192, 75, 0.6)' for value in difference_values]

    # HTML content generation
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
            .hidden {{
                display: none;
            }}
            .zero-difference {{
                background-color: lightgreen;
            }}
        </style>
        <!-- Include Chart.js library -->
        <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    </head>
    <body>
        <h2>{title}</h2>
        <!-- Summary statistics -->
        <p>Number of Matches: {match_count}</p>
        <p>Number of Mismatches: {mismatch_count}</p>
        <p>Average Mismatch Difference: {average_mismatch_difference:.2f}</p>
        <!-- Expandable table section -->
        <p>Comparison Detail: <a href="javascript:void(0);" onclick="toggleTable()">[Expand]</a></p>
        <div id="comparisonTable" class="hidden">
            <table>
                <tr>
                    <th>Pixel</th>
                    <th>DUT Result</th>
                    <th>Pytorch Result</th>
                    <th>Difference</th>
                </tr>
    """

    for entry in report:
        line = entry['line']
        hex_value = entry['hex_value']
        dec_value = entry['dec_value']
        difference = entry['difference']
        
        # Apply class to highlight zero difference rows
        if difference == 0:
            difference_class = 'zero-difference'
        else:
            difference_class = ''

        html_content += f"""
                <tr class="{difference_class}">
                    <td>{line}</td>
                    <td>{hex_value}</td>
                    <td>{dec_value}</td>
                    <td>{difference}</td>
                </tr>
        """

    html_content += """
            </table>
        </div>
        
        <!-- Total of Difference Chart: Expand -->
        <p>Total of Difference Chart: <a href="javascript:void(0);" onclick="toggleChart()">[Expand]</a></p>
        <div id="differenceChartContainer" class="hidden">
            <!-- Chart canvas -->
            <canvas id="differenceChart" width="800" height="400"></canvas>
            <script>
                // JavaScript to create and display the bar chart
                var ctx = document.getElementById('differenceChart').getContext('2d');
                var differenceChart = new Chart(ctx, {
                    type: 'bar',
                    data: {
                        labels: """ + str(difference_values) + """,
                        datasets: [{
                            label: 'Count of Differences',
                            data: """ + str(difference_counts_values) + """,
                            backgroundColor: """ + str(bar_colors) + """,
                            borderColor: 'rgba(54, 162, 235, 1)',
                            borderWidth: 1
                        }]
                    },
                    options: {
                        responsive: true,
                        scales: {
                            xAxes: [{
                                type: 'linear',
                                position: 'bottom',
                                scaleLabel: {
                                    display: true,
                                    labelString: 'Absolute Difference Value'
                                },
                                ticks: {
                                    beginAtZero: false,
                                    stepSize: 1,
                                    min: 1 // Ensure x-axis starts from 1
                                }
                            }],
                            yAxes: [{
                                scaleLabel: {
                                    display: true,
                                    labelString: 'Count'
                                },
                                ticks: {
                                    beginAtZero: true,
                                    stepSize: 1
                                }
                            }]
                        }
                    }
                });

                // Function to toggle visibility of the difference chart
                function toggleChart() {
                    var chartContainer = document.getElementById('differenceChartContainer');
                    chartContainer.classList.toggle('hidden');
                }
            </script>
        </div>

        <script>
            // Function to toggle visibility of the comparison table
            function toggleTable() {
                var table = document.getElementById('comparisonTable');
                table.classList.toggle('hidden');
            }
        </script>
    </body>
    </html>
    """
    
    with open(output_path, 'w') as file:
        file.write(html_content)




for i in range(24):
    # File paths
    hex_file_path = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/real_results/DUT_out_channel_{i}.txt'
    dec_file_path = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/expected_results/Expected_out_channel_{i}.txt'
    output_path   = f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_Evaluation/conv1_output/result_compare/comparison_report_{i}.html'
    
    # Perform comparison and generate HTML report
    report, match_count, mismatch_count, average_mismatch_difference = compare_files(hex_file_path, dec_file_path)
    generate_html_report(report, match_count, mismatch_count, average_mismatch_difference, output_path, f'Channel {i}')
    
    print(f"Comparison report generated: {output_path}")

