#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>


void do_sigmoid(svLogicVecVal *copyIn);

void golden_model( svLogicVecVal *sigmoid_rslt, const svLogicVecVal *in) {
    svLogicVecVal *copyIn;
    copyIn->aval = in->aval;
    copyIn->bval = in->bval;
    // do sigmoid function
    do_sigmoid(copyIn);
    // copy value to send to SV
    sigmoid_rslt->aval = copyIn->aval;
    sigmoid_rslt->bval = copyIn->bval;
}

void do_sigmoid(svLogicVecVal *copyIn){
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

    copyIn->aval = abs(copyIn->aval);           // |x|
    sign_bit = svGetBitselLogic(copyIn, 31);    // save the sign bit 
    if( copyIn->aval >= fp_5_0.aval ) {
        copyIn->aval = fp_1_0.aval;
        copyIn->bval = fp_1_0.bval;
	return;
    } 
    else if( copyIn->aval >= fp_2_375.aval ) {
        shift_amount = 5;
        plan_operand.aval = fp_0_84375.aval;	
        plan_operand.bval = fp_0_84375.bval;	
    } 
    else if( copyIn->aval >= fp_1_0.aval ) {
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
    copyIn->aval >>= shift_amount;
    copyIn->bval >>= shift_amount;
    for(int i = 0; i < shift_amount; i++) 
        svPutBitselLogic(copyIn, 32-shift_amount+i, sign_bit);		// add sign bits after shift as shift right remove right bits
    // Add PLAN operand									
    copyIn->aval += plan_operand.aval;
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
