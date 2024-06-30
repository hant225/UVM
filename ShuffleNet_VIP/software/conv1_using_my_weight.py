import torch
import os
import csv

from fxpmath import Fxp
from torchvision.io import read_image
from torchvision.models.quantization import shufflenet_v2_x0_5, ShuffleNet_V2_X0_5_QuantizedWeights

# Define the model without loading default weights
model = shufflenet_v2_x0_5(weights=None, quantize=True)

# Load your custom weights
custom_weights_path = '/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/delete_later/shufflenet_v2_custom_weights.pth'
model.load_state_dict(torch.load(custom_weights_path))

# Ensure the model is in evaluation mode
model.eval()

# Read the image
img = read_image("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/dataset/airplaner.jpg")

# Define the preprocessing transform (use transforms that match your training setup)
preprocess = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT.transforms(antialias=True)

# Preprocess the image and create a batch
batch = preprocess(img).unsqueeze(0)

# Perform the prediction
with torch.no_grad():
    prediction = model(batch).squeeze(0).softmax(0)

# Get the predicted class and score
class_id = prediction.argmax().item()
score = prediction[class_id].item()
category_name = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT.meta["categories"][class_id]
print(f"{category_name}: {100 * score}%")

# Define the hook function to save conv1 output
def save_conv1_output(module, input, output):
    data = input[0].int_repr()
    output_int = output.int_repr()
    output_int = output_int.detach().cpu()

    batch_size, num_channels, height, width = output_int.shape
    flattened_outputs = output_int.view(batch_size, num_channels, -1)
    
    for i, channel_data in enumerate(flattened_outputs[0]):
        with open(f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/out_channel_{i}.txt', 'w') as f:
            f.write('\n'.join(map(str, channel_data.numpy())))

# Register the hook to save conv1 output
if hasattr(model, 'conv1'):
    model.conv1.register_forward_hook(save_conv1_output)

# Perform a forward pass to trigger the hook and save the conv1 output
with torch.no_grad():
    output = model(batch)

