
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
   loop invariant a == 2*x + r*r - r;
   loop invariant 0 <= x;
   loop invariant 0 <= r;
   loop assigns x;
   loop assigns r;
   ```c;
   ```;
   Looking at this code, I need to generate loop invariants that maintain the relationship between the variables throughout the loop execution.;
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert a == 2*x + r*r - r; */
}
