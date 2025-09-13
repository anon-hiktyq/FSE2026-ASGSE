
int main30(int x,int y,int n) {
    // variable declarations
    int z=0;
    int w=0;
    int p=0;

    // precondition
    /*@ requires (p == 0) && (w == 0) && (z == 0) && (n == \at(n,Pre)) && (y == \at(y,Pre)) && (x == \at(x,Pre)); */

    /*@
      loop invariant (\at(n,Pre) > 0) ==> (z == (\at(n,Pre) - n) * (x * x));
      loop invariant (\at(n,Pre) > 0) ==> (w == (\at(n,Pre) - n) * (y * y));
      loop invariant (\at(n,Pre) > 0) ==> (p == (\at(n,Pre) - n) * (x * y));
      loop invariant (!(\at(n,Pre) > 0)) ==> ((p == 0)&&(w == 0)&&(z == 0)&&(n == \at(n,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant y == \at(y,Pre);
      loop invariant x == \at(x,Pre);
      loop assigns z, w, p, n;
    */
    while(n > 0) {
        z = z + x * x;
        w = w + y * y;
        p = p + x * y;
        n -= 1;
    }
    
    // post-condition
    /*@ assert z * w >= p * p; */
}
