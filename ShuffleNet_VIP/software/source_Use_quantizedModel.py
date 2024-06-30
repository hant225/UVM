import torch
import os
import csv
import matplotlib.pyplot as plt

from fxpmath import Fxp
from torchvision.io import read_image
from torchvision.models.quantization import shufflenet_v2_x0_5, ShuffleNet_V2_X0_5_QuantizedWeights

# Step 1: Initialize model with the best available weights
weights = ShuffleNet_V2_X0_5_QuantizedWeights.DEFAULT
model = shufflenet_v2_x0_5(weights=weights, quantize=True)

# Truy cập lớp conv1
conv1 = model.conv1 # Lớp Conv2d đầu tiên trong Sequential của conv1
# maxpool = model.maxpool


#print("hehe: ",conv1)
#print("hehe: ",conv1._weight_bias()[0])


# In ra weights
# print("Weights of conv1:", conv1.weight()) #.int_repr()
# print("size: ", conv1.weight().size())

# # Kiểm tra xem có bias không và in ra nếu có
# if conv1.bias() is not None:
#     print("Bias of conv1:", conv1.bias())
#     print("size: ", conv1.bias().dtype)
# else:
#     print("No bias in conv1 layer.")

#===============================================trích xuất trọng số conv1=================================================

# output_dir = "D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\weights\conv1"

# # Lặp qua từng kênh
# for i in range(conv1.weight().size(0)):
#     weight_set = conv1.weight()[i].int_repr()

#     # Chuyển tensor đã dequantize sang NumPy
#     weight_set_np = weight_set.numpy()

#     file_path = os.path.join(output_dir, f"channel_{i}.csv")

#     # Ghi ra file CSV
#     with open(file_path, mode='w', newline='') as file:
#         writer = csv.writer(file)
        
#         # Ghi từng giá trị ra file CSV
#         for weight_matrix in weight_set_np:
#             for row in weight_matrix:
#                 writer.writerow(row)
#===============================================trích xuất weight conv1=================================================

# Kích thước của tensor
# num_filters, num_channels, height, width = conv1.weight().shape
# num_ultra_ram = num_filters*num_channels/8

# # Duyệt qua tensor
# with open('D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\weights\convDW_stage2_1_branch2_3_fp\export_weight.txt', 'w') as f:
#     group = []  # Khởi tạo danh sách nhóm trọng số
#     for idx_height in range(height):
#         for idx_width in range(width):
#             for idx_filter in range(num_filters):
#                 for idx_num_channel in range(num_channels):
#                     # Trích xuất giá trị trọng số dưới dạng số nguyên
#                     weight_value = conv1.weight().int_repr()[idx_filter, idx_num_channel, idx_height, idx_width].item()
#                     fxp_weight = Fxp(weight_value, signed=True, n_word=8, n_frac=0)
#                     group.append(fxp_weight.hex()[2:].lower())  # Chuyển sang hex và bỏ '0x'
#     # Chuyển danh sách nhóm trọng số thành chuỗi
#     full_string = ''.join(group)
#     for i in range(0, len(full_string), 16):
#         line = full_string[i:i+16]
#         # Đảo ngược thứ tự các byte
#         reversed_line = ''.join([line[j:j+2] for j in range(0, 16, 2)][::-1])
#         f.write(reversed_line + '\n')
#===============================================trích xuất weight conv1=================================================

#===============================================trích xuất dequant_scale conv1=================================================
# print(conv1.scale)
# print(conv1.zero_point)

# Giả sử conv1 là lớp Conv2d đã được lượng tử hóa
# Lấy giá trị scale từ lớp lượng tử hóa, giả sử nó là một giá trị float hoặc một tensor với một phần tử
# scale_value = conv1.scale  # Đảm bảo rằng scale_value là float

# print(scale_value)
# if isinstance(scale_value, torch.Tensor):
#     scale_value = scale_value.item()  # Chuyển tensor một phần tử thành float

# # Tạo một đối tượng Fxp từ giá trị scale này
# fxp_scale = Fxp(scale_value, signed=False, n_word=64, n_frac=32)

# # In ra biểu diễn hex và nhị phân
# hex_value = fxp_scale.hex()[2:].lower()  # Bỏ '0x'
# print("Hexadecimal format:", hex_value)

# # Ghi giá trị này vào file txt
# with open('D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\weights\convDW_stage2_0_branch1_2_fp\export_scale.txt', 'w') as file:
#     file.write(hex_value)
#===============================================trích xuất dequant_scale conv1=================================================


#===============================================trích xuất bias conv1=================================================

# print("Bias of conv1:", conv1.bias())
# print("Bias of conv1:")

# for value in conv1.bias():
#     fxp_weight = Fxp(value.item(), signed=True, n_word=32, n_frac=16)
#     # print(f"{value.item():.10f}")
#     print(fxp_weight.hex()[2:].lower())


# with open('D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\weights\convDW_stage2_1_branch2_3_fp\export_bias.txt', 'w') as f:
#     group = []  # Khởi tạo danh sách nhóm bias
#     for b in conv1.bias().detach():
#         # Chuyển giá trị bias sang dạng số học cố định và lấy dạng hex, bỏ '0x'
#         fxp_weight = Fxp(b.item(), signed=True, n_word=32, n_frac=16)
#         group.append(fxp_weight.hex()[2:].lower())

#     # Ghi vào file, ghép từng cặp hex và xuống dòng mới cho mỗi cặp
#     for i in range(0, len(group), 2):
#         # Kiểm tra nếu còn phần tử cuối cùng không đủ cặp
#         if i+1 < len(group):
#             line = group[i+1] + group[i]  # Ghép cặp, đổi thứ tự ghép
#         else:
#             line = group[i]  # Chỉ có một phần tử cuối cùng
#         f.write(line + '\n')

#=============================================== end trích xuất bias conv1=================================================

model.eval()

img = read_image(".\\airplaner.jpg")

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

#================================================================================================

# # Định nghĩa một hook để in ra scale và zero_point
# def print_quant_params(module, input, output):
#     print(f"Quantizing with scale: {module.scale}, zero_point: {module.zero_point}")

# # Đính hook này vào QuantStub
# if hasattr(model, 'quant'):
#     model.quant.register_forward_hook(print_quant_params)

# # Tạo một tensor đầu vào giả lập
# input_tensor = torch.rand(1, 3, 224, 224)  # Giả sử đầu vào có kích thước 224x224x3

# # Đưa tensor qua mô hình và quan sát các thông số lượng tử
# with torch.no_grad():
#     output = model(input_tensor)
#================================================================================================


#===========================================export output conv1===================================================== hay su dung

def save_conv1_output(module, input, output):
    # output is a quantized tensor with datatype like torch.quint8
    data = input[0].int_repr()  # Get integer representation of the quantized data
    # Mở file để ghi
    # with open("D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\pixels\ShuffleUnit_Short_stage2_1.txt", "w") as txt_file:
    #     # Chuyển đổi và ghi dữ liệu
    #     channels = data.shape[1]  # Số kênh
    #     height = data.shape[2]    # Chiều cao
    #     width = data.shape[3]     # Chiều rộng
    #     for h in range(height):
    #         for w in range(width):
    #             line = []
    #             for c in reversed(range(channels)):
    #                 pixel = data[0, c, h, w].item()  # Lấy giá trị pixel
    #                 fxp_pixel = Fxp(pixel, signed=False, n_word=8, n_frac=0)
    #                 line.append(fxp_pixel.hex()[2:].lower())  # Chuyển sang hex và bỏ '0x'
    #             txt_file.write(''.join(line) + '\n')  # Ghi vào file
    # =========================================================================================
    # Convert it to integer representation
    output_int = output.int_repr()
    
    # Move the tensor to cpu
    output_int = output_int.detach().cpu()

    #Flatten the tensor to one dimension per channel
    batch_size, num_channels, height, width = output_int.shape
    flattened_outputs = output_int.view(batch_size, num_channels, -1)
    
    # Save each channel's data to a text file
    for i, channel_data in enumerate(flattened_outputs[0]):
        with open(f'D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\\results\ShuffleUnit_Short_stage2_1\Software\output_quant\\out_channel_{i}.txt', 'w') as f:
            # Write the data for the current channel to a file
            f.write('\n'.join(map(str, channel_data.numpy())))

# Kiểm tra xem model có thuộc tính conv1 không
if hasattr(model, 'conv1'):
    # Đăng ký hook cho layer conv1
    conv1.register_forward_hook(save_conv1_output)
# 
# if hasattr(model, 'stage2') and \
#    hasattr(model.stage2, '2') and \
#    hasattr(model.stage2[2], 'branch2') and \
#    hasattr(model.stage2[2].branch2, '0'):
#     print("complete")
#     conv1.register_forward_hook(save_conv1_output)

# if hasattr(model, 'stage2') and \
#    hasattr(model.stage2, '1'):
#     print("complete")
#     conv1.register_forward_hook(save_conv1_output)


# Tính toán đầu ra với batch đầu vào
with torch.no_grad():
    output = model(batch)




#===========================================end export output conv1=====================================================

# Định nghĩa một hook để in ra đầu ra từ lớp convolution đầu tiên
def extract_quant_output(module, input, output):
    # Lấy đại diện số nguyên của tensor output
    output_data = output#.int_repr()
    print("Output from the quant layer: ", output_data)
    print(output_data.dtype)
    # # Hiển thị mỗi kênh dưới dạng hình ảnh
    # num_channels = output_data.size(1)  # Giả sử output có dạng (N, C, H, W)
    # num_cols = 6  # Số cột trong hiển thị
    # num_rows = (num_channels + num_cols - 1) // num_cols  # Tính số hàng cần thiết
    
    # fig, axes = plt.subplots(num_rows, num_cols, figsize=(num_cols*2, num_rows*2))  # Điều chỉnh kích thước figure
    # axes = axes.flatten()  # Chuyển axes thành mảng một chiều
    # for i in range(num_channels):
    #     channel_data = output_data[0, i].numpy()  # Lấy dữ liệu của kênh thứ i và chuyển sang NumPy array
    #     ax = axes[i]
    #     im = ax.imshow(channel_data, cmap='gray', interpolation='nearest',vmin=0, vmax=255)
    #     ax.axis('off')
    #     ax.set_title(f'Channel {i}')
    
    # for i in range(num_channels, len(axes)):
    #     axes[i].axis('off')  # Ẩn các axes không sử dụng
    
    # plt.subplots_adjust(wspace=0.2, hspace=0.2)  # Giảm khoảng cách giữa các hình
    # plt.show()

# # Gắn hook vào lớp conv đầu tiên
# # Ví dụ: giả sử lớp conv đầu tiên là 'model.conv1[0]'
# if hasattr(model, 'conv1'):
#     model.conv1[0].register_forward_hook(extract_quant_output)
# if hasattr(model, 'quant'):
#     model.quant.register_forward_hook(extract_quant_output)
# # Đưa tensor qua mô hình và quan sát đầu ra từ hook
# with torch.no_grad():
#     output = model(batch)

#=============================================export data===================================================

# Định nghĩa hook
def extract_quant_output(module, input, output):
    data = output.int_repr()  # Get integer representation of the quantized data
    # Mở file để ghi
    with open("D:\Workspace\Learning\KLTN\code\software\ShuffleNet_V2\data\pixels\pixel_image.txt", "w") as txt_file:
        # Chuyển đổi và ghi dữ liệu
        channels = data.shape[1]  # Số kênh
        height = data.shape[2]    # Chiều cao
        width = data.shape[3]     # Chiều rộng
        for h in range(height):
            for w in range(width):
                line = []
                for c in reversed(range(channels)):
                    pixel = data[0, c, h, w].item()  # Lấy giá trị pixel
                    fxp_pixel = Fxp(pixel, signed=False, n_word=8, n_frac=0)
                    line.append(fxp_pixel.hex()[2:].lower())  # Chuyển sang hex và bỏ '0x'
                txt_file.write(''.join(line) + '\n')  # Ghi vào file

# Đăng ký hook vào model.quant
# if hasattr(model, 'quant'):
#     model.quant.register_forward_hook(extract_quant_output)

# # Đưa tensor qua mô hình và quan sát đầu ra từ hook
# with torch.no_grad():
#     output = model(batch)
    
#================================================================================================

#================================================================================================

