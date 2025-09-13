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
   loop invariant x >= 0;
   loop invariant r >= 0;
   loop invariant x + (r * (r - 1)) / 2 == a / 2;
   loop invariant (r + 1) * (r + 1) >= a;
   loop assigns x, r;
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert (r+1) * (r+1) >= a; */
}
