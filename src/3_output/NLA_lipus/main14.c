
#include <stdlib.h>

/*@
  predicate valid_non_negative(int a, int b) = (a >= 0 && b >= 0);
*/

/*@
    requires valid_non_negative(a, b);
*/
int main14(int a, int b) {
    int x = a;
    int y = b;
    int z = 0;

    /*@
      loop invariant (\at(b,Pre) != 0) ==> (y >= 0 && y <= \at(b,Pre));
      loop invariant (\at(b,Pre) != 0) ==> (z + y * x == a * b);
      loop invariant (!(\at(b,Pre) != 0) ) ==> ((z == 0) && (y == \at(b,Pre)) && (x == \at(a,Pre)) && (b == \at(b,Pre)) && (a == \at(a,Pre)));
      loop invariant b == \at(b,Pre);
      loop invariant a == \at(a,Pre);
      loop assigns z, x, y;
    */
    while (y != 0) {
        if (y % 2 == 1) {
            z = z + x;
            y = y - 1;
        }
        x = 2 * x;
        y = y / 2;
    }

    /*@ assert z == a * b; */
}
