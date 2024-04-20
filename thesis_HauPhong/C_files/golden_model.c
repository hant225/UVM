#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>



void c_mac(const svLogicVecVal *pixel_data, 
	   const svLogicVecVal *weight_data, 
	   const svLogicVecVal *reg_data,
	   svLogicVecVal *mac_out )
{
    svLogicVecVal *p;
    svLogic sign_bit;
    // do 8 bits mul, result is 16 bit
    p->aval = pixel_data->aval * weight_data->aval;
    p->bval = pixel_data->bval * weight_data->bval;

    // bit extending
    sign_bit = svGetBitselLogic(p, 15);    // save the sign bit    
    for(int i = 0; i < 16; i++)
        svPutBitselLogic(p, 16 + i, sign_bit);
    // do 32 bits adder
    mac_out->aval = reg_data->aval + p->aval; 
    mac_out->bval = reg_data->bval + p->bval; 
}

void c_dequantize(const svLogicVecVal *deq_in, const svLogicVecVal *scale, svLogicVecVal *deq_out){
    svLogicVecVal *p;
    p->aval = deq_in->aval * scale->aval;
    p->bval = deq_in->bval * scale->bval;
    printf("[DEC] %0d\n", *p);
    printf("[HEX] %0x\n", *p);
    printf("[BIN] %0b\n", *p);
}

void c_bias(const svLogicVecVal *bias_in, const svLogicVecVal *bias_weight, svLogicVecVal *bias_out){
    bias_out->aval = bias_in->aval + bias_weight->aval;	
    bias_out->bval = bias_in->bval + bias_weight->bval;	
}

void c_sigmoid(svLogicVecVal *actv_in, svLogicVecVal *actv_out){
    // Copy input
    actv_out->aval = actv_in->aval;
    actv_out->bval = actv_in->bval;    
    //  constant fixed point numbers using in sigmoid
    const svLogicVecVal fp_5_0     = { .aval = 0b00000000000001010000000000000000,
                                       .bval = 0 };
    const svLogicVecVal fp_1_0     = { .aval = 0b00000000000000010000000000000000,
                                       .bval = 0 };
    const svLogicVecVal fp_2_375   = { .aval = 0b00000000000000100110000000000000,
                                       .bval = 0 };
    const svLogicVecVal fp_0_84375 = { .aval = 0b00000000000000001101100000000000,
                                       .bval = 0 };
    const svLogicVecVal fp_0_625   = { .aval = 0b00000000000000001010000000000000,
                                       .bval = 0 };
    const svLogicVecVal fp_0_5     = { .aval = 0b00000000000000001000000000000000,
                                       .bval = 0 };
    
    int shift_amount;
    svLogic sign_bit;
    svLogicVecVal plan_operand;

    actv_out->aval = abs(actv_out->aval);                // |x|
    sign_bit = svGetBitselLogic(actv_out, 31);           // save the sign bit 
    if( actv_out->aval >= fp_5_0.aval ) {
        actv_out->aval = fp_1_0.aval;
        actv_out->bval = fp_1_0.bval;
	return;
    } 
    else if( actv_out->aval >= fp_2_375.aval ) {
        shift_amount = 5;
        plan_operand.aval = fp_0_84375.aval;	
        plan_operand.bval = fp_0_84375.bval;	
    } 
    else if( actv_out->aval >= fp_1_0.aval ) {
        shift_amount = 3;
        plan_operand.aval = fp_0_625.aval;	
        plan_operand.bval = fp_0_625.bval;	
    } 
    else {
        shift_amount = 2;
        plan_operand.aval = fp_0_5.aval;	
        plan_operand.bval = fp_0_5.bval;	
    }
    
    // Do shift
    actv_out->aval >>= shift_amount;
    actv_out->bval >>= shift_amount;
    for(int i = 0; i < shift_amount; i++) 
        svPutBitselLogic(actv_out, 32-shift_amount+i, sign_bit);		// add sign bits after shift as shift right remove right bits
    // Add PLAN operand									
    actv_out->aval += plan_operand.aval;
}

void c_quantize(svLogicVecVal *quant_in, svLogicVecVal *quant_out){
   svLogic bit_16th;
   bit_16th = svGetBitselLogic(quant_in, 16);

   if(bit_16th) 
       quant_out->aval = 0xFFFFFFFF;
   else
       svGetPartselLogic(quant_out, quant_in, 8, 8);

   quant_out->bval = 0xFFFFFF00;
}










/////////////////////////////////////////////////////////////////////////////////////////////////
// Function for testing things //////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////

void test_thang(){
    svLogicVecVal o1;
    svLogicVecVal o2;

    svLogicVecVal fp_2_375;     
    svLogicVecVal fp_0_84375; 
    svLogicVecVal fp_0_625;     
    svLogicVecVal fp_0_5;   
    
    fp_2_375.aval   =  0b00000000000000100110000000000000;
    fp_0_84375.aval =  0b00000000000000001101100000000000;
    fp_0_625.aval   =  0b00000000000000001010000000000000;
    fp_0_5.aval     =  0b00000000000000001000000000000000;    
    
    o1.aval = -25;
    o2.aval = -50;    
    o1.bval = 0;
    o2.bval = 0;

    printf("%0d + %0d = %0d\n", o1.aval, o2.aval, o1.aval + o2.aval);
    printf("%0d - %0d = %0d\n", o1.aval, o2.aval, o1.aval - o2.aval);
    printf("%0d * %0d = %0d\n", o1.aval, o2.aval, o1.aval * o2.aval);

    if(o1.aval > o2.aval)
        printf("o1:%0d is larger than o2:%0d\n", o1.aval, o2.aval);
    else if(o1.aval < o2.aval)
        printf("o1:%0d is less than o2:%0d\n", o1.aval, o2.aval);
    else
        printf("o1:%0d and o2:%0d is equal\n", o1.aval, o2.aval);

    printf("abs(o1) = %0d\n", abs(o1.aval));
    printf("before abs(o1) : %0b\n", o1.aval);
    printf("after abs(o1)  : %0b\n", abs(o1.aval));
}
