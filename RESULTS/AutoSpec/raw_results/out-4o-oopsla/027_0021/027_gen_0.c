
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l <= i <= n;
    loop invariant 1 <= k < n;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}