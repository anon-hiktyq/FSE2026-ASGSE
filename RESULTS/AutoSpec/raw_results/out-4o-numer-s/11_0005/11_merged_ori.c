//svcomp_diamond_2-2

void hoo11(int y){
    int x = 0;

    //pre-condition
    
    //loop-body
    /*@
    loop invariant x >= -5 * (y % 2 == 1 ? (99 / 5) + 1 : 0);;
    loop invariant x <= 99;
    loop invariant x <= 10 * (x;
    loop invariant x <= 10 * (99 / 10);;
    loop invariant x <= 10 * ((99 - x) / 10);;
    loop invariant x < 99;
    loop invariant x % 2 == y % 2;
    loop invariant 10 * (x < 0 ? -x / 5 : x / 10);
    loop invariant 0 ? -x / 5 : x / 10) <= x;
    loop invariant -5 * (x < 0 ? -x / 5 : x / 10);
    loop invariant -5 * (99 / 5) <= x;
    loop invariant -5 * (100 / 15) <= x;
    loop invariant -5 * ((99 - x) / 5) <= x;
    loop invariant -5 * ((99 - x) / 10) <= x;
    loop invariant -5 * ((99 - x + 4) / 5) <= x && x <= 10 * (99 - x) / 10;
    loop invariant -495 <= x;
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