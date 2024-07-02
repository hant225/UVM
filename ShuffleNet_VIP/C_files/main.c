#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>


void gen_conv1_input_and_rslt() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/cnn_my_verification/Python_files/conv1_randIimg_and_refModel.py");
}

void golden_model() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/cnn_my_verification/Python_files/compare_to_pytorch_rslt.py");
}
