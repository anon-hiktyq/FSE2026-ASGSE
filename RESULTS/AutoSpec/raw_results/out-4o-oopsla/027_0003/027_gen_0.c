
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= k);
  loop invariant \forall integer j; 0 <= j < k ==> (1 <= k);
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant i >= l;
    loop invariant i <= n;
    loop invariant k < n;
    loop invariant \forall integer j; l <= j < i ==> (1 <= k);
    loop invariant \exists integer j; l <= j < i && i == l;
    loop invariant \forall integer j; i <= j < n ==> (1 <= k);
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant \forall integer j; l <= j < i ==> (1 <= k);
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}