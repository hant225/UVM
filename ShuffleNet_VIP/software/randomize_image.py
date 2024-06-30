import random

# Define the number of times to generate the random numbers
num_iterations = 224

# Open a file to write the random numbers
with open('gen_img.txt', 'w') as file:
    for _ in range(num_iterations * num_iterations):
        random_numbers = [random.randint(0, 255) for _ in range(3)]
        file.write(f"{random_numbers[0]:<4} {random_numbers[1]:<4}  {random_numbers[2]:<4}\n")


