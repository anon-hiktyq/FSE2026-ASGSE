//svcomp_benchmark47_linear
int unknown();
/*@
  requires x < y;
  requires y <= 20000001;
*/
void hoo17(int x,int y){
    

    //pre-condition
    //loop-body
    /*@
    loop invariant y >= 0 ==> y % 3 == (y - \at(y,Pre)) % 3;
    loop invariant y <= 20000001;
    loop invariant y < 0 ==> y % 10 == (y - \at(y,Pre)) % 10;
    loop invariant x >= 0 ==> x % 10 == (x - \at(x,Pre)) % 10;
    loop invariant x <= y;
    loop invariant x <= y + 16;
    loop invariant x <= \old(x) + ((y - \old(y)) + 17);
    loop invariant x < y;
    loop invariant x < y + 20;
    loop invariant x < y + 17;
    loop invariant x < y + 16;
    loop invariant x < 20000001;
    loop invariant x < 0 ==> x % 7 == (x - \at(x,Pre)) % 7;
    loop invariant \old(y) <= y;
    loop invariant \old(x); <= x;
    loop invariant \old(x) <= x;
    loop invariant \at(x,Pre) <= x;
    loop assigns y;
    loop assigns x;
    */
    while (x < y) {
        if (x < 0){
            x = x + 7; 
        }
        else {
            x = x + 10;
        }
        if (y < 0){
            y = y - 10;
        } 
        else {
            y = y + 3;
        }

    }

    //post-condition
    /*@ assert x <= y + 16; */
}