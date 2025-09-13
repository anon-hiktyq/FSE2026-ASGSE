
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant 1 <= k <= n;
  loop invariant l > 0;
  loop invariant \forall integer j; 1 <= j < k ==> (l <= i < n) ==> (1 <= j);
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}