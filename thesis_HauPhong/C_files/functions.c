#include <stdio.h>
#include <stdlib.h>
#include <svdpi.h>
#include <math.h>

int myCFunc1(){ return 5; }
int myCFunc2(int A, int *B) {
    *B = A/2;
    return A*2;
}
double myCFunction3( int A, float B, double C ) {
    return (double)A+(double)(B)+C;
}
double mySin( double C ) { return sin(C); }
double myCos( double C ) { return cos(C); }
double myTan( double C ) { return tan(C); }

// Function to check adder
int plus8bit(int a, int b){
    if(a + b > 255)
        printf("[C] %0d + %0d = %0d (Overflowed)\n", a, b, a+b);
    else
	printf("[C] %0d + %0d = %0d\n", a, b, a+b);

    return a + b;
}

// Function to test shift left and right
void  c_shift(svLogicVecVal *B) {
    printf("[C-BIN]  B = %0d\n", *B);
    //svLogicVecVal *B;

    B->aval = -100000;
    printf("Before shift %0d\n", *B);
    printf("Before shift %0b\n", *B);

    printf("\nUSING >> OPERATOR\n");
    svLogic sign_bit;
    sign_bit = 1;
    B->aval >>= 1;
    B->bval >>= 1;
    svPutBitselLogic(B, 31, sign_bit);
    printf("After shift %0d\n", *B);
    printf("After shift %0b\n", *B);

    //printf("\nUSING / OPERATOR\n");
    //B->aval = -100000;
    //printf("Before shift %0d\n", *B);
    //B->aval = B->aval / 2;
    //printf("B div 2: %d\n", *B);
    //printf("B div 2: %b\n", *B);
}

void func_for_test(svLogicVecVal *A, svLogicVecVal *sub_A){
    //svLogicVecVal *sub_A;

    printf("[C-BIN]  A = %0d\n", *A);  
    printf("[C-BIN]  A = %0b\n", *A);  

    //int left, right;
    //left = svLeft(A, 1);
    //printf("svLeft(A, 1) = %d\n", left);  
    //right = svRight(A, 1);
    //printf("svRight(A, 1) = %0d\n", right);  

    svGetPartselLogic(sub_A, A, 4, 8);
    printf("[C]  sub_A after GetPartselLogic = %b\n", *sub_A);
    printf("[C]  sub_A->aval = %b\n", sub_A->aval);
    printf("[C]  sub_A->bval = %b\n", sub_A->bval);
   
    svLogic sign_bit;
    sign_bit = 1;
    for(int j = 8; j < 12; j++) {
    	printf("[i%0d]padding sign bit\n", j);
	svPutBitselLogic(sub_A, j, sign_bit);
    }
    sub_A->aval >>= 4;
    sub_A->bval >>= 4;
    //svPutPartselLogic(sub_A, *sub_A, 6, 4);
    //printf("[C]  sub_A after PutPartselLogic= %0b\n", *sub_A);
}

void do_shift(svLogicVecVal *A, svBit do_shift_right, int shift_amount, svLogicVecVal *result){
    int iA;
    iA = A->aval;
    svLogic sign_bit;
    sign_bit = svGetBitselLogic(A, 31);    // get sign bit of A
    if(do_shift_right){
	A->aval >>= shift_amount;
	A->bval >>= shift_amount;
        for(int i = 0; i < shift_amount; i++) {
	    svPutBitselLogic(A, 32-shift_amount+i, sign_bit);
    	    printf("[i%0d]padding sign bit\n", i);
	}
	result->aval = A->aval;
	printf("%0d shift right %0d bits = %0d\n", iA, shift_amount, *result);
    } else {
	A->aval <<= shift_amount;
	A->bval <<= shift_amount;
	result->aval = A->aval;
        printf("%0d shift left %0d bits = %0d\n", iA, shift_amount, *result);
    }
}

void test_thang(){
    svLogicVecVal *tmp;
    tmp->aval = 0b00000000000000100110000000000000;
    printf("tmp = %0b\n", *tmp);
    printf("tmp = %0d\n", *tmp);
    svLogicVecVal tmp1;
    svLogicVecVal tmp2;
    svLogicVecVal tmp3;
    tmp1.aval = 123;
    tmp2.aval = 456;
    tmp3.aval = 789;

    svLogicVecVal fp_2_375;     
    svLogicVecVal fp_0_84375; 
    svLogicVecVal fp_0_625;     
    svLogicVecVal fp_0_5;   

    fp_2_375.aval   =  0b00000000000000100110000000000000;
    fp_0_84375.aval =  0b00000000000000001101100000000000;
    fp_0_625.aval   =  0b00000000000000001010000000000000;
    fp_0_5.aval     =  0b00000000000000001000000000000000; 
    printf("fp_2_375   aval: %b\n", fp_2_375  . aval);
    printf("fp_2_375   bval: %b\n", fp_2_375  . bval);
    printf("fp_0_84375 aval: %b\n", fp_0_84375.aval);
    printf("fp_0_84375 bval: %b\n", fp_0_84375.bval);
    printf("fp_0_625   aval: %b\n", fp_0_625  . aval);
    printf("fp_0_625   bval: %b\n", fp_0_625  . bval);
    printf("fp_0_5     aval: %b\n", fp_0_5    . aval);
    printf("fp_0_5     bval: %b\n", fp_0_5    . bval);

}








