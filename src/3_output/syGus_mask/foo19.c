
void foo19(int n,int z1,int z2,int z3) {
    int x = 0;
    int m = 0;

    /*@
      loop invariant 0 <= x <= n;
      loop invariant m == \at(m,Pre) || (0 <= m < x && \forall integer k; 0 <= k < x ==> (!unknown() || m == k));
      loop invariant z1 == \at(z1,Pre);
      loop invariant z2 == \at(z2,Pre);
      loop invariant z3 == \at(z3,Pre);
      loop invariant n == \at(n,Pre);
      loop assigns x, m;
      loop variant n - x;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }
}
