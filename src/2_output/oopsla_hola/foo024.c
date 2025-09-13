
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo024(int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int i,j,k;
  
  i=0;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0<n@pre) => (0 <= i && i < n)) &&
((!(0<n@pre)) => ((i == 0)&&(n == n@pre))) &&
(n == n@pre
              loop assigns \nothing)
    */
    
            for (i=0;i<n;i++){

    j=i;
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              // Loop invariant: At the start of each iteration of the loop over j,
              // we have that j >= i and j < n.
              loop invariant i <= j < n;
              loop assigns \nothing;
            */
            for (j=i;j<n;j++){

      k=j;
      
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              // Loop invariant: At the start of each iteration of the loop over k,
              // we have that k >= j and k < n.
              loop assigns \nothing;
            */
            for (k=j;k<n;k++){
	       /*@assert k >= i;*/
      }
            
    }
            
  }
}