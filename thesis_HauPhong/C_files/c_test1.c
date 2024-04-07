// C Code

#include <stdio.h>
#include "svdpi.h"

extern  void f(
    const svBitVecVal* fa,
    const svBitVecVal* fs,
    const svBitVecVal* fu,
    const svBit* fb,
    svLogic fl0,
    const svLogic fl1,
    const svLogic flz,
    const svLogic flx,
    svLogicVecVal* flpa
    )
    	
  {
    int i;
    printf("fa is %d, fs is %d, fu is %d\n", *fa, *fs, *fu);

    for (i = 0; i < 10; i++)
      printf("b[%0d] is %0d\n", i, fb[i]);

   
    fl0 = fl0 + 100;
    flpa = flpa + flpa;

    printf("l0 = %0d\n", fl0);
    printf("l1 = %0d\n", fl1);
    printf("lz = %0d\n", flz);
    printf("lx = %0d\n", flx);
    
    printf("lpa.aval = %0x\n", flpa->aval);
    printf("lpa.bval = %0x\n", flpa->bval);


    
    printf("\n");
    
  }

