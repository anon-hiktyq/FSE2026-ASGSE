
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer m; 1 <= m < k ==> (l <= m < n) ==> (1 <= m);
  loop invariant \forall integer j; 1 <= j < k ==> (l <= i < n) ==> (1 <= j);
  loop invariant \forall integer i; l <= i < n ==> 1 <= k;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l < n;
    loop invariant i == l || \forall integer m; l <= m < i ==> l <= m < n;
    loop invariant i <= n;;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m <= i ==> (1 <= k);
    loop invariant 0 <= i;
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}