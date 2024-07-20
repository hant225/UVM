#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>

// CONV1 ----------------------------------------------------------------------------------------------------------------------------------------
void gen_conv1_input_and_rslt() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/conv1_randImg_and_refModel.py");
}                            

void conv1_golden_model() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/conv1_compare_to_pytorch_rslt.py");
}


// CONVDW ---------------------------------------------------------------------------------------------------------------------------------------
void gen_convDW_input_and_rslt() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/convDW_randImg_and_refModel.py");
}          

void convDW_golden_model() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/convDW_compare_to_pytorch_rslt.py");
}

// CONV1x1 ---------------------------------------------------------------------------------------------------------------------------------------
void gen_conv1x1_input_and_rslt() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/conv1x1_randImg_and_refModel.py");
}          

void conv1x1_golden_model() {
    system("/usr/bin/python3 /home/hao/Documents/0.KHOA_LUAN_TOT_NGHIEP/shuffle_net/ShuffleNet_VIP/Python_files/conv1x1_compare_to_pytorch_rslt.py");
}
