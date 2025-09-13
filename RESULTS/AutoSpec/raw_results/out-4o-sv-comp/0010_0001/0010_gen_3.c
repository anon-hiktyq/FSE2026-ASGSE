
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
    loop invariant y == j - 2*(i - x);
    loop invariant z == i - x;
    loop invariant z >= 0;
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
