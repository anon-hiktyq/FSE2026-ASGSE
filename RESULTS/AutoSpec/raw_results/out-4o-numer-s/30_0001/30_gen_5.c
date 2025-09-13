
/*@
  requires a % 2 == 0;
  requires a > 0;
*/
void hoo30(int a) {
    // variable declarations
   int x, r;
    //precondition
   r = 0;
   x = a / 2;

    // loop body
   /*@
   loop invariant 0 <= r <= x; 
   loop invariant a == 2*x + r*r - r;
   loop assigns x, r;
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert a == 2*x + r*r - r; */
}
