import torch
import os
import csv
import matplotlib.pyplot as plt

from fxpmath import Fxp
from torchvision.io import read_image
from torchvision.models.quantization import shufflenet_v2_x0_5, ShuffleNet_V2_X0_5_QuantizedWeights
from torchvision.models import ShuffleNet_V2_X0_5_Weights

export_weights_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/software/pretrained_weights.txt"
modified_weight_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/software/modified_pretrained_weights.pth" 


# Step 1: Initialize model with the best available weights
bQuantize = True     # Choosing Export Quantized or Default Pre-trained Weights

if bQuantize:
    weights = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT
    model = shufflenet_v2_x0_5(weights=weights, quantize=True)
    export_weights_path = "/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/software/pretrained_QuantizedWeights.txt"
else:
    weights = ShuffleNet_V2_X0_5_Weights.DEFAULT
    model = shufflenet_v2_x0_5(weights=weights, quantize=False)


# Step 2: Export weight to pth file
state_dict = weights.get_state_dict()

with open(export_weights_path, 'w') as file:
    print(state_dict, file=file)

print(f"State dict written to {export_weights_path}")


# ------------------------------------ Utilities ------------------------------------

### Print all keys of the state_dict
for key in state_dict.keys():
   print(key)

### Print tensor values as int8
selected_key = "conv1.0.weight"
print(state_dict[selected_key].int_repr())

### Print tensor dimension
print(state_dict[selected_key].shape)

# -----------------------------------------------------------------------------------




 
### Save the modified weights
torch.save(state_dict, modified_weight_path)
print(f"Modified state dict save to {modified_weight_path}")

