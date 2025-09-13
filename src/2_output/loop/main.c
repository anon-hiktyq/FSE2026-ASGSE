
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    

int main()

/*@

Require emp

Ensure Results(__return)
*/{
  int i;
  int N=100000;
  int a[2*N+2];

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for(i=0;i<=N;i++) {
    a[2*i]=0;
    a[2*i+1]=0;
  }


  
    
  
}