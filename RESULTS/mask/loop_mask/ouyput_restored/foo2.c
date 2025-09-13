
void foo2(int y, int z)
{
    int x = 0;

    /*@
      loop invariant ((x == 0) && (z == \at(z,Pre)) && (y == \at(y,Pre))) || 
                      ((x > 0) && (z == \at(z,Pre)) && ((z <= \at(y,Pre)) ==> (y == z)) && ((z > \at(y,Pre)) ==> (y == \at(y,Pre))));
      loop invariant 0 <= x <= 500;
      loop invariant z == \at(z,Pre);
      loop assigns x, y;
      loop variant 500 - x;
    */
    while(x < 500) {
        x += 1;
        if(z <= y) {
            y = z;
        }
    }
    /*@ assert z >= y; */

    /* mask_1 */
}
