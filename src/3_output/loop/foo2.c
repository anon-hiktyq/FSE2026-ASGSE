
void foo2(int y, int z)
{
    int x = 0;   

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant 0 <= x <= 500;
      loop invariant z == \at(z,Pre);
      loop invariant (x == 0 && y == \at(y,Pre)) || (z >= y);
    */
    while(x < 500) {
        x += 1;
        if(z <= y) {
            y = z;
        }
    }

    /*@ assert z >= y; */
}
