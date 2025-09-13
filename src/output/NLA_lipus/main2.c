
/*@
  predicate valid_division(int x, int y, int q, int r) = 
      0 <= r < y && x == y * q + r;

*/

/*@ 
    requires x > 0;
    requires y > 0;
*/
int main2(int x,int y){
 
  int q = 0;
  int r = 0;
  
  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant 0 <= q;
    loop invariant 0 <= r < y;
    loop invariant (x == y * q + r) || (x > y * q + r);
    loop invariant y == \at(y, Pre);
    loop invariant x == \at(x, Pre);
  */
  while (x > y * q + r) {
      if (r == y - 1) {
          r = 0;
          q += 1;
      } else {
          r += 1;
      }
  }
  
  /*@ assert q == x / y; */
}
