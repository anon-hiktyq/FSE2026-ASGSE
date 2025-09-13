/*@
requires i >= 0 && j >= 0;
*/
int foo(int i, int j) {
    //int i;
    //int j;


    int x = i;
    int y = j;
    
    /*@
    loop invariant y == j - (i - x);
    loop invariant x >= 0 && y >= 0;
    loop invariant x == 0 ==> y == j - i;
    loop invariant x <= i;
    loop invariant x + y == i + j;
    loop invariant j - (i - x) <= y;
    loop invariant \forall integer k; 0 <= k <= i - x ==> y == j - k;
    loop invariant 0 <= x;
    loop invariant (x == 0) ==> (y == j - i);
    loop assigns y;
    loop assigns x;
    */
    while (x != 0) {
    	x--;
    	y--;
    }

    if (i == j) {
    	// @ assert y == 0;
    }
    
    return 0;
}
