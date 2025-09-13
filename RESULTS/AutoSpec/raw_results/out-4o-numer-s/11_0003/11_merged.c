//svcomp_diamond_2-2

void hoo11(int y){
    int x = 0;

    //pre-condition
    
    //loop-body
    /*@
    loop invariant 10 * ((x < 99) ? (99 / 10) : 0);
    loop invariant -5 * (99/5) <= x;
    loop invariant -5 * (99 / 5) <= x;
    loop invariant -5 * ((99 - x) / 5) <= x;
    loop invariant (y % 2 == 0 ==> x % 10 == 0);
    loop invariant (y % 2 != 0 ==> x % 5 == 0);
    loop assigns x;
    */
    while (x < 99) {
        if (y % 2 == 0) 
            x += 10;
        else 
            x -= 5;
    }

    //post-condition
    /*@ assert (x % 2) == (y % 2); */
}