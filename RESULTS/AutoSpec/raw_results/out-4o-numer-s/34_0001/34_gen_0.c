//freire1.c
/*@
  requires a % 2 == 0;
  requires a > 0;
*/
void hoo34(int a){
  // variable declarations
 int x, r;
  //precondition
 r = 0;
 x = a / 2;

  // loop body
 /*@
 loop invariant 0 <= r <= a / 2;
 loop invariant x == a / 2 - (r * (r - 1)) / 2;
 loop invariant x >= 0;
 loop assigns x;
 loop assigns r;
 */
 while (x > r){
     x = x - r;
     r = r + 1;
 }
  // post-condition
  /*@ assert (r-1) * (r-1) <= a; */
}
