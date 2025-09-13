//svcomp_Mono4_1
int unknown();

void hoo19(){
    int x = 0;
    int y = 500000;

    //loop-body
    /*@
    loop invariant y == 500000 || y == x;
    loop invariant y == 500000 + (x - 500000) * (x >= 500000);
    loop invariant y <= x;
    loop invariant y <= x + 500000;
    loop invariant y <= 1000000;
    loop invariant y - x == 500000;
    loop invariant x >= 500000 ==> y == x;
    loop invariant x <= y;
    loop invariant x <= 1000000;
    loop invariant x < 500000 ==> y == 500000;
    loop invariant 500000 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
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