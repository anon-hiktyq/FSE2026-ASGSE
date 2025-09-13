
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo61(int x, int y, int k, int j, int i, int n) 

            /*@
            Require x + y == k && n > 0
            Ensure Results(__return)
            */
            {
 
  int m = 0;
  j = 0;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (x + y == k)) &&
((0 < n@pre) => (0 <= j && j <= n)) &&
((0 < n@pre) => (m == 0 || (0 <= m && m < j))) &&
((0 < n@pre) => (((m == 0)&&(n == n@pre)&&(i == i@pre)&&(j == 0)&&(k == k@pre)&&(y == y@pre)&&(x == x@pre)) || ((m == 0 || (0 <= m && m < j)) && (x + y == k)))) &&
((!(0 < n@pre)) => ((m == 0)&&(n == n@pre)&&(i == i@pre)&&(j == 0)&&(k == k@pre)&&(y == y@pre)&&(x == x@pre))) &&
(n == n@pre) &&
(i == i@pre) &&
(k == k@pre
      loop assigns j, x, y, m
      loop variant n - j)
    */
    
  while (j < n) {
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (unknown()){
       m = j;
    }
    j++;
  }
  
  
  
  

}