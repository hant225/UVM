import torch
import os
import csv

from fxpmath import Fxp
from torchvision.io import read_image
from torchvision.models.quantization import shufflenet_v2_x0_5, ShuffleNet_V2_X0_5_QuantizedWeights

#-------------------------------------------------------------------------------
# function: conv1x1
# Author: HauPhong
# Reuse: Hao Ngo
#-------------------------------------------------------------------------------

# Step 1: Initialize model with the best available weights
weights = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT
model = shufflenet_v2_x0_5(weights=weights, quantize=True)

# conv1 layer access
conv1 = model.conv1 

model.eval()

# img = read_image("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/dataset/airplaner.jpg")
img = read_image("output_image.png")

# Step 2: Initialize the inference transforms
preprocess = weights.transforms(antialias=True)

# Step 3: Apply inference preprocessing transforms
batch = preprocess(img).unsqueeze(0)

# print(quantized_batch) #.int_repr()
# Step 4: Use the model and print the predicted category
prediction = model(batch).squeeze(0).softmax(0)
class_id = prediction.argmax().item()
score = prediction[class_id].item()
category_name = weights.meta["categories"][class_id]
print(f"{category_name}: {100 * score}%")



#================================== export output conv1 =================================

def save_conv1_output(module, input, output):
    # output is a quantized tensor with datatype like torch.quint8
    data = input[0].int_repr()  # Get integer representation of the quantized data
    # Convert it to integer representation
    output_int = output.int_repr()
    
    # Move the tensor to cpu
    output_int = output_int.detach().cpu()

    #Flatten the tensor to one dimension per channel
    batch_size, num_channels, height, width = output_int.shape
    flattened_outputs = output_int.view(batch_size, num_channels, -1)
    
    # Save each channel's data to a text file
    for i, channel_data in enumerate(flattened_outputs[0]):
        with open(f'/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/conv1_output/conv1_expected_results/out_channel_{i}.txt', 'w') as f:
            # Write the data for the current channel to a file
            f.write('\n'.join(map(str, channel_data.numpy())))

# Check if the model had conv1 attribute or not
if hasattr(model, 'conv1'):
    # Register hook for conv1 layer
    conv1.register_forward_hook(save_conv1_output)


# Calculating output with input batch
with torch.no_grad():
    output = model(batch)
#================================ end export output conv1 ==============================






# # Định nghĩa một hook để in ra đầu ra từ lớp convolution đầu tiên
# def extract_quant_output(module, input, output):
#     # Lấy đại diện số nguyên của tensor output
#     output_data = output#.int_repr()
#     print("Output from the quant layer: ", output_data)
#     print(output_data.dtype)
# #=============================================export data===================================================
# #####################################################################################################
# ###                                                                                               ###
# ###  Hao note: Doan code ben duoi de combine 3 kenh anh cua 1 pixel thanh 1 dong trong output     ###
# ###  Vi du: O pixel dau tien vi tri 0x0 co  R = 79, G = 71, B = 6a => pixel1 = 79716a             ###
# ###                                                                                               ###
# #####################################################################################################
# 
# # Định nghĩa hook
# def extract_quant_output(module, input, output):
#     data = output.int_repr()  # Get integer representation of the quantized data
#     # Mở file để ghi
#     with open("/home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/pixels/pixel_image.txt", "w") as txt_file:
#         # Chuyển đổi và ghi dữ liệu
#         channels = data.shape[1]  # Số kênh
#         height = data.shape[2]    # Chiều cao
#         width = data.shape[3]     # Chiều rộng
#         for h in range(height):
#             for w in range(width):
#                 line = []
#                 for c in reversed(range(channels)):
#                     pixel = data[0, c, h, w].item()  # Lấy giá trị pixel
#                     fxp_pixel = Fxp(pixel, signed=False, n_word=8, n_frac=0)
#                     line.append(fxp_pixel.hex()[2:].lower())  # Chuyển sang hex và bỏ '0x'
#                 txt_file.write(''.join(line) + '\n')  # Ghi vào file
# 
# #================================================================================================

