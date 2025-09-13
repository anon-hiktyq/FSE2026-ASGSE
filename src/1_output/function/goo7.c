
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void func7(int *a, int n) /*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure emp
*/
{
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, n, a_l) && n > 0 && n < 100 &&
    ((!(i < n@pre)) => ((n == n@pre) && (a == a@pre))) &&
(n == n@pre) &&
(a == a@pre
    loop assigns a_l[0 .. n-1], i)
    */
    
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}
void goo7() 
/*@

Require emp

Ensure emp
*/{
    int arr[5] = {1, 2, 3, 4, 5};
    func7(arr, 5);



}