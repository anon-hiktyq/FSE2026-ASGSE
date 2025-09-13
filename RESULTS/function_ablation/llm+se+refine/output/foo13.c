
void foo13(int n,int z1,int z2,int z3)
{
    int x = 1;
    int m = 1;

    /*@
      loop invariant (m >= 1) && (m <= x);
      loop invariant (n > 1) ==> (m < n);
      loop invariant (z1 == \at(z1,Pre)) && (z2 == \at(z2,Pre)) && (z3 == \at(z3,Pre)) && (n == \at(n,Pre));
      loop assigns x, m;
      loop variant n - x;
    */
    while (x < n) {

        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }

    /*@ assert (n > 0) ==> (m < n); */
}
