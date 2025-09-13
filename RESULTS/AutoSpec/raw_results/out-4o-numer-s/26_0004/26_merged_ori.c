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
   loop invariant x == a / 2 - (r * (r + 1)) / 2;
   loop invariant x + r * (r - 1) / 2 == a / 2;
   loop invariant x + r * (r + 1) / 2 == a / 2;
   loop invariant x + (r * (r - 1)) / 2 == a / 2;
   loop invariant a <= (r + 1) * (r + 1);
   loop invariant 0 <= x;
   loop invariant 0 <= r;
   loop invariant (r + 1) * (r + 1) >= a || r * r < a;
   loop invariant (r + 1) * (r + 1) >= a ==> r * (r - 1) / 2 <= a / 2;
   loop assigns x;
   loop assigns r;
   */
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    /*@ assert (r+1) * (r+1) >= a; */
}
