// jm2006_variant_true-unreach-call.c

/*@
requires 0 <= i && i < 1000000;
requires j >= 0;
*/
int foo(int i, int j) {
    //int i;
    //int j;
    

    int x = i;
    int y = j;
    int z = 0;
    
    /*@
    loop invariant z == i - x;
    loop invariant y == j - 2*z;
    loop invariant y == j - 2 * z;
    loop invariant x + z == i;
    loop invariant 0 <= z;
    loop invariant 0 <= x;
    loop assigns z;
    loop assigns y;
    loop assigns x;
    */
    while (x != 0) {
    	x--;
    	y -= 2;
    	z++;
    }

    if (i == j) {
    	//@ assert y == -z;
    }
    
    return 0;
}
