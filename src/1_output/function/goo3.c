
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void increment_array_by(int* arr, int n, int c) /*@
With arr_l
Require store_int_array(arr, n, arr_l) && n > 0 && n < 100
Ensure emp
*/
{
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  arr_l,    
    store_int_array(arr, n, arr_l) && n > 0 && n < 100 &&
    ((!(i < n)) => ((c == c)&&(n == n)&&(arr == arr))) &&
(c == c) &&
(n == n) &&
(arr == arr) &&
(0 <= i && i <= n
    loop assigns arr_l[0 .. n-1], i)
    */
    
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}
void goo3() 
/*@

Require emp

Ensure emp
*/{
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);





}