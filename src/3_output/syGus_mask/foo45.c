
/*@
    requires n > 0;
    ensures \true; // Removed ensures clause involving c
*/
void foo45(int n) {

    int c = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (n > 0) ==> (((c == 0) && (n == \at(n,Pre))) || (0 < c <= n));
      loop invariant (\at(n,Pre) > 0) ==> (n == \at(n,Pre));
      loop assigns c;
    */
    while (unknown()) {
        {
          if (unknown()) {
            if (c != n) {
              c = c + 1;
            }
          } else {
            if (c == n) {
              c = 1;
            }
          }
        }
    }
}
