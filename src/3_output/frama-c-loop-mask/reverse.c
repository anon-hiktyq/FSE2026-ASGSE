
/*@
axiomatic Reverse_array {
  logic integer reverse_index(integer n, integer i) = n - 1 - i;
}
*/

/*@
requires \valid(a + (0 .. n-1));
requires n > 0 && n < 100;
*/
void reverse(int *a, int n) {
    int i = 0;
    int j = n-1;

    /*@ 
      loop invariant 0 <= i <= n/2;
      loop invariant j == n - 1 - i;
      loop invariant n == \at(n,Pre);
      loop invariant a == \at(a,Pre);
    */
    while (i < n/2) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
        i++;
        j--;
    }
}
