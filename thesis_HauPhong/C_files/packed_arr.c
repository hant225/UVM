#include <stdio.h>
#include <stdlib.h>
#include "svdpi.h"

extern void get_nums(svLogicVecVal a[10]){
    svLogic i;
    for(i = 0; i < 10; i++) {
    	printf("[%0d]\n", i);
	a[i] = i*2;
    }
}
