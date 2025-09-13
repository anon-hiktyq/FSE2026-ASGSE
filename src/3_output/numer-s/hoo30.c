
/*@
    requires a % 2 == 0;
    requires a > 0;
    */
    
int hoo30(int a) {
    // variable declarations
    int x, r;
    //precondition
    r = 0;
    x = a / 2;

    // loop body
    /*@
        loop invariant (\at(a,Pre) / 2 > 0) ==> (x >= 0);
        loop invariant (\at(a,Pre) / 2 > 0) ==> (r >= 0);
        loop invariant (\at(a,Pre) / 2 > 0) ==> (a == 2*x + r*(r - 1));
        loop invariant (!(\at(a,Pre) / 2 > 0)) ==> ((r == 0) && (x == \at(a,Pre) / 2) && (a == \at(a,Pre)));
        loop invariant a == \at(a,Pre);
        loop assigns x, r;
    */
    while (x > r){
        x = x - r;
        r = r + 1;
    }
    
    // post-condition
    /*@ assert a == 2*x + r*r - r; */
}
