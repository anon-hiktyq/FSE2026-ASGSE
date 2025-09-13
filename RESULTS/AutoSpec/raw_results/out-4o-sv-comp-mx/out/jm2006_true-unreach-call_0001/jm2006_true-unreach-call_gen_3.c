/*@
requires i >= 0 && j >= 0;
*/
int foo(int i, int j) {
    //int i;
    //int j;


    int x = i;
    int y = j;
    
    /*@
    loop invariant x >= 0;
    loop invariant y == j - (i - x);
    loop invariant (x == 0) ==> (y == j - i);
    loop assigns x, y;
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
