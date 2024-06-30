from PIL import Image
import numpy as np

# Define the size of the image
width, height = 224, 224

# Initialize an empty list to store the RGB values
rgb_values = []

# Open and read the text file
with open('gen_img.txt', 'r') as file:
    for line in file:
        r, g, b = map(int, line.strip().split())
        rgb_values.append((r, g, b))

# Ensure the number of RGB values matches the expected size
assert len(rgb_values) == width * height, "The number of RGB values does not match the expected image size."

# Create a NumPy array from the list of RGB values
rgb_array = np.array(rgb_values, dtype=np.uint8).reshape((height, width, 3))

# Create an image from the NumPy array
image = Image.fromarray(rgb_array, 'RGB')

# Save or display the image
image.save('output_image.png')
image.show()  # This will open the image using the default image viewer

