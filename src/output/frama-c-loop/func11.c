
int func11(int n) {
    int sum = 0;
    int i = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant !(0 <= \at(n,Pre)/2) ==> (i == 0 && sum == 0);
      loop invariant 0 <= i <= n/2;
      loop invariant sum == 2 * (i * (i + 1) / 2);
      loop assigns sum, i;
      loop variant n/2 - i;
    */
    while(i <= n/2) {
        sum = sum + 2*(i);
        i++;
    }
    
    /*@
      ensures n < 0 ==> \result == 0;
      ensures n >= 0 ==> \result == n * (n / 2 + 1);
    */
    return sum;
}
