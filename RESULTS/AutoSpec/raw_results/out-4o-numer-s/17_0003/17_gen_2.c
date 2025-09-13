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
    loop invariant x < y + 17;
    loop invariant x < y;
    loop invariant x >= \old(x);
    loop invariant y <= \old(y) + ((\old(y) < 0) ? 0 : (3 * (\old(y) - y) / 13));
    loop assigns x, y;
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