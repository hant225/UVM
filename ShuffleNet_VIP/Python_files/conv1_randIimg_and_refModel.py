import torch
import os
import csv
import random

from fxpmath import Fxp
from torchvision.io import read_image
from torchvision.models.quantization import shufflenet_v2_x0_5, ShuffleNet_V2_X0_5_QuantizedWeights

#-----------------------------------------------------------------------------------------
# function: conv1x1									  
# Author: HauPhong									  
# Reuse: Hao Ngo								          
# Description:									          
#    - This code choose a random number and get the corresponding img to that number      
#    - The image go to Pytorch model first and get the output of CONV1 stage		  
#    - The image after preprocess and quantize is export as input for the CONV1 DUT	  
#-----------------------------------------------------------------------------------------

# Step 1: Initialize model with the best available weights
weights = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT
model = shufflenet_v2_x0_5(weights=weights, quantize=True)

# conv1 layer access
conv1 = model.conv1 

model.eval()

# Random an image
seed = random.randint(1, 10)
img = read_image(f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/dataset/{seed}.jpg')
print(f'random image at \"/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/dataset/{seed}.jpg\"')

# Step 2: Initialize the inference transforms
preprocess = weights.transforms(antialias=True)

# Step 3: Apply inference preprocessing transforms
batch = preprocess(img).unsqueeze(0)

# Step 4: Use the model and print the predicted category
prediction = model(batch).squeeze(0).softmax(0)
class_id = prediction.argmax().item()
score = prediction[class_id].item()
category_name = weights.meta["categories"][class_id]
print(f"{category_name}: {100 * score}%")

input_path  = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/cnn_my_verification/InputData/"
output_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/conv1_expected_results/"

def save_conv1_output(module, input, output):
    # 1.Export Image Data for DUT  ================================================================================================================================
    ### Convert it to integer representation
    data = input[0].int_repr()                                               # Get integer representation of the quantized data
    
    ### output is a quantized tensor with datatype like torch.quint8
    with open(f'{input_path}/pixel_image.txt', 'w') as txt_file:             # Open file to write
        # Chuyển đổi và ghi dữ liệu
        channels = data.shape[1]     # channel_in
        height   = data.shape[2]     # height
        width    = data.shape[3]     # width
        for h in range(height):
            for w in range(width):
                line = []
                for c in reversed(range(channels)):
                    pixel = data[0, c, h, w].item()                           # extract pixel data
                    fxp_pixel = Fxp(pixel, signed=False, n_word=8, n_frac=0)
                    line.append(fxp_pixel.hex()[2:].lower())                  # convert to hex and remove '0x' part
                txt_file.write(''.join(line) + '\n')                          # write to file
    
    # 2.Export Expect Result ======================================================================================================================================
    output_int = output.int_repr()                                            # Convert it to integer representation
    output_int = output_int.detach().cpu()                                    # Move the tensor to cpu
    batch_size, num_channels, height, width = output_int.shape                # Flatten the tensor to one dimension per channel
    flattened_outputs = output_int.view(batch_size, num_channels, -1)
    ### Save each channel's data to a text file
    for i, channel_data in enumerate(flattened_outputs[0]):
        with open(f'{output_path}/Expected_out_channel_{i}.txt', 'w') as f:
            f.write('\n'.join(map(str, channel_data.numpy())))                # Write the data for the current channel to a file



# Check if the model had conv1 attribute or not
if hasattr(model, 'conv1'):
    # Register hook for conv1 layer
    conv1.register_forward_hook(save_conv1_output)


# Calculating output with input batch
with torch.no_grad():
    output = model(batch)

