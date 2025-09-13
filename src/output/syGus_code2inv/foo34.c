
void foo34(int n,int v1,int v2,int v3) {

    int x = n;
    
    /*@
      loop invariant n >= 0 ==> (x >= 0);
      loop invariant x == \at(n, Pre) - (n - \at(n, Pre) + (\at(n, Pre) - x));
      loop assigns x;
    */
    while (x > 0) {
        x = x - 1;
    }
    
   /*@ assert (n >= 0) ==> (x == 0); */
}
