
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo044(int k, int flag , int __BLAST_NONDET) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int i=0;
  int j=0;
  int n;
 

  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 <= k@pre) => (0 <= i && i <= k + 1)) &&
((0 <= k@pre) => (j == i * n)) &&
((!(0 <= k@pre)) => ((j == 0) && (i == 0) && (__BLAST_NONDET == __BLAST_NONDET@pre) && (flag == flag@pre) && (k == k@pre))) &&
((flag == 1) => (n == 1)) &&
((flag != 1) => (n == 2)) &&
(__BLAST_NONDET == __BLAST_NONDET@pre) &&
(flag == flag@pre) &&
(k == k@pre
    loop assigns i, j)
    */
    
  while ( i <= k) {
    i++;
    j = j + n;
  }
  
    
	
}