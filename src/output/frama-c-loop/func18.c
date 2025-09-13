
/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0..n-1];
  ensures \forall integer j; 0 <= j < n ==> (j % 2 == 0 ==> a[j] == 0);
  ensures \forall integer j; 0 <= j < n ==> (j % 2 == 1 ==> a[j] == \at(a[j], Pre));
*/
void func18(int *a, int n) {
    
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 0 ==> a[j] == 0);
      loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 1 ==> a[j] == \at(a[j], Pre));
      loop assigns a[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}
