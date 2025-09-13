
void reverse(int *a, int n) {
    int i = 0;
    int j = n-1;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (0 < \at(n,Pre)/2) ==> (0 <= i <= \at(n,Pre)/2);
      loop invariant !(0 < \at(n,Pre)/2) ==> ((j == \at(n,Pre) - 1) && (i == 0) && (n == \at(n,Pre)) && (a == \at(a,Pre)));
      loop invariant n == \at(n,Pre);
      loop invariant a == \at(a,Pre);
      loop assigns i, j, a[0..n-1];
    */
    while (i < n/2) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
        i++;
        j--;
    }
}
