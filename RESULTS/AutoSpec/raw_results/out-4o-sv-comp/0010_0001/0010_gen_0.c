
/*@
requires 0 <= i && i < 1000000;
requires j >= 0;
*/
void foo0010(int i, int j) {

    int x = i;
    int y = j;
    int z = 0;
  
    /*@
    loop invariant x >= 0;
    loop invariant y + 2 * x == j;
    loop invariant z == i - x;
    loop invariant x + z == i;
    loop assigns x;
    loop assigns y;
    loop assigns z;
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
