//svcomp_Mono4_1
int unknown();

void hoo19(){
    int x = 0;
    int y = 500000;

    //loop-body
    /*@
    loop invariant 0 <= x <= 1000000;
    loop invariant x <= y <= x + 500000;
    loop invariant y == 500000 || y == x;
    loop assigns x, y;
    */
    while(x < 1000000) {
	    if (x < 500000) {
	        x = x + 1;
	    } 
        else {
            x = x + 1;
            y = y + 1;
	    }
    }

    //post-condition
    /*@ assert y == x; */
}