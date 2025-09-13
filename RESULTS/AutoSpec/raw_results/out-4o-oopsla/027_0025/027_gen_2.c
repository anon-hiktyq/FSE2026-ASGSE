
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer m; l <= m < i ==> l <= m;
  loop invariant \forall integer j; l <= j < n ==> k >= 1;
  loop invariant \forall integer j; l <= j < n ==> 1 <= k;
  loop invariant \forall integer j; l <= j < n ==> 0 < l;
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; l <= j < k ==> (1 <= k);
  loop invariant \forall integer j; l <= j < i ==> 1 <= k;
  loop invariant \forall integer j; l <= j < i ==> (1 <= k);
  loop invariant \forall integer j; 1 <= j < k ==> (l <= i);
  loop invariant \forall integer j; 0 <= j < k ==> 1 <= k;
  loop invariant \exists integer m; l <= m < i ==> k >= 1;
  loop invariant 1 <= k;
  loop invariant 0 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l <= i;
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop invariant k == 1 + \at(k, Pre);
    loop invariant \forall integer m; l <= m < i ==> l <= m;
    loop invariant \forall integer j; l <= j < i ==> 1 <= k;
    loop invariant \exists integer m; l <= m < i ==> k >= 1;
    loop assigns i;
    loop assigns k;
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant \forall integer m; i <= m < n ==> l <= m;
    loop invariant \forall integer j; l <= j < n ==> (1 <= k);
    loop invariant \forall integer j; l <= j < i ==> 1 <= k;
    loop invariant \forall integer j; l <= j < i ==> (1 <= k);
    loop invariant 1 <= k;
    loop invariant 0 < n;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}