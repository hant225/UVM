# Example of using sigmoid activation in a neural network layer
import numpy as np

def sigmoid(x):
    return 1 / (1 + np.exp(-x))

# Example of computing the output of a neuron using sigmoid activation
input_data = np.array([0.5, 0.7, 0.2])  # Example input data
weights = np.array([0.3, -0.1, 0.8])    # Example weights
bias = 0.1                              # Example bias

# Compute the weighted sum
weighted_sum = np.dot(input_data, weights) + bias

print("Weighted_sum: ", weighted_sum)

# Apply sigmoid activation function
output = sigmoid(weighted_sum)

print("Output:", output)

