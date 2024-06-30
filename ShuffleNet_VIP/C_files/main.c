#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>


void call_pytorch() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/cnn_my_verification/Python_files/generate_image.py");
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/cnn_my_verification/Python_files/conv1_quantizedModel.py");
}

