#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>



void c_mac(const int pixel_data, 
	   const int weight_data, 
	   const int reg_data,
	   svLogicVecVal *mac_out )
{
    mac_out->aval = pixel_data * weight_data + reg_data;
    mac_out->bval = 0;
}

/*void c_bias(const svLogicVecVal *bias_in, const svLogicVecVal *bias_weight, svLogicVecVal *bias_out){
    bias_out->aval = bias_in->aval + bias_weight->aval;	
    bias_out->bval = bias_in->bval + bias_weight->bval;	
}*/

void c_bias(const int bias_in, 
	    const int bias_weight, 
	    svLogicVecVal *bias_out)
{
    bias_out->aval = bias_in + bias_weight;
    bias_out->bval = 0;
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

void test_thang(const signed int ia, const signed int ib, svLogicVecVal *s, svLogicVecVal *p){
    s->aval = ia + ib;
    s->bval = 0;
    p->aval = ia * ib;
    p->bval = 0;
    printf("[C] %0d +/* %0d = \n", ia, ib);
}
    

