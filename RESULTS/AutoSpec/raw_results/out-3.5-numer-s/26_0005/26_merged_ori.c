/*@
  requires a % 2 == 0;
  requires a > 0;
*/
void hoo26(int a) {
    // variable declarations
    int x = a / 2;
    int r = 0;

    // loop body
   /*@
   loop invariant x + r*(r+1)/2 == a/2;
   loop invariant 0 <= x;
   loop invariant 0 <= r;
   loop assigns x;
   loop assigns r;
   ```c;
   ```;
   The function starts with `x = a / 2` and `r = 0`, then in each iteration decreases `x` by `r` and increments `r`. The loop continues while `x > r`.;
   Looking at this function, I need to analyze what the loop does and what properties hold throughout its execution.;
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert (r+1) * (r+1) >= a; */
}
