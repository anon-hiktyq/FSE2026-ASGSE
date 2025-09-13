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
 loop invariant 0 <= r <= x;
 loop invariant x >= 0;
 loop invariant r >= 0;
 loop invariant a == 2*x + 2*r*r - 2*r;
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
