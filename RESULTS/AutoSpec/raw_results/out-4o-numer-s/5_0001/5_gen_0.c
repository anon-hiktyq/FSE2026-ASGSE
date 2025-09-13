//svcomp_eq1
/*@
  requires x > 0;
  requires y > 0;
  requires z > 0;
  requires w > 0;
*/
void hoo5(int a,int w,int x,int y,int z) {
    //pre-condition
    x = w;
    z = y;
 
    /*@
    loop invariant x == w;
    loop invariant y == z;
    loop invariant w > 0;
    loop invariant x > 0;
    loop invariant y > 0;
    loop invariant z > 0;
    loop assigns w, x, y, z;
    */
    while(unknown()) {
        if (unknown()) {
            w = w + 1; 
            x = x + 1;
        } 
        else {
            y = y - 1; 
            z = z - 1;
        }
    }

    //post-condition
    /*@ assert y == z; */
}