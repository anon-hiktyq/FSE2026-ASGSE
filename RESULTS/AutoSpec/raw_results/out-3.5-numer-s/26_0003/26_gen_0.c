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
   Looking at this function, I need to analyze what the loop is doing and what properties hold throughout its execution.
   
   The function starts with `x = a/2` and `r = 0`, then in each iteration decreases `x` by `r` and increments `r` by 1. The loop continues while `x > r`.
   
   ```c
   loop invariant x + r*(r+1)/2 == a/2;
   loop invariant r >= 0;
   loop invariant x >= 0;
   loop assigns x, r;
   ```
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert (r+1) * (r+1) >= a; */
}
