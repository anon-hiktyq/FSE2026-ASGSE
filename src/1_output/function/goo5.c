
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int arraysearch5(int* a, int x, int n) /*@
With a_l
Require store_int_array(a, x, a_l) && x > 0 && x < 100
Ensure Results(__return)
*/
{ 

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, x, a_l) && x > 0 && x < 100 &&
    ((!(p < n)) => ((n > 0) && (x > 0 && x < 100) && \valid(a + (0 .. n-1)))) &&
(n > 0) &&
(x > 0 && x < 100) &&
(\valid(a + (0 .. n-1))
      loop assigns p
      loop variant n - p)
    */
    
    for (int p = 0; p < n; p++) {
        if (x == a[p]) 
            return 1;
    }
  return 0;
}
void goo5() 
/*@

Require emp

Ensure emp
*/{
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = arraysearch5(arr, 3, 5);

}