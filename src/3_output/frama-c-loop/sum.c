
int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
      loop invariant 0 <= k;
      loop invariant k <= n + 1;
      loop invariant s == \sum{i=0..k-1} (int)i;
      loop variant n - k;
    */
    while(k <= n) {    
        s = s + (int)k;
        k = k + 1;
    }
            
    return (int)s;
}
