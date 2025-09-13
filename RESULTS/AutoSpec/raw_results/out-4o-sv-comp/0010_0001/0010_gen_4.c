
/*@
requires 0 <= i && i < 1000000;
requires j >= 0;
*/
void foo0010(int i, int j) {

    int x = i;
    int y = j;
    int z = 0;
  
    /*@
    loop invariant 0 <= x <= i;
    loop invariant z == i - x;
    loop invariant y == j - 2*z;
    loop invariant x >= 0;
    loop invariant y >= -2*i;
    loop assigns x, y, z;
    */
    while (x != 0) {
        x--;
        y -= 2;
        z++;
    }

    if (i == j) {
        // @ assert y == -z;
    }
    
}
