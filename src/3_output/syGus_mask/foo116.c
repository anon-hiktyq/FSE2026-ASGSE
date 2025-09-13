
void foo116(int v1,int v2,int v3) {

    int sn = 0;
    int x = 0;
    
    /*@
      loop invariant sn == x;
      loop invariant sn >= 0;
      loop invariant x >= 0;
      loop invariant v3 == \at(v3,Pre);
      loop invariant v2 == \at(v2,Pre);
      loop invariant v1 == \at(v1,Pre);
      loop assigns x, sn;
    */
    while (unknown()) {
        x = x + 1;
        sn = sn + 1;
    }
}
