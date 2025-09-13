
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
    loop invariant k == 1 + \at(k, Pre);
    loop invariant i == l || i == n;
    loop invariant i <= n;
    loop invariant i <= n;
    loop invariant i <= n || i < n;
    loop invariant i <= n || 0 <= i;
    loop invariant i < n;
    loop invariant i < n;
    loop invariant i < n || 0 <= i;
    loop invariant \forall integer m; l <= m <= i ==> m >= l;
    loop invariant \forall integer m; l <= m <= i ==> l <= m;
    loop invariant \forall integer m; l <= m < n ==> l <= m;
    loop invariant \forall integer m; l <= m < i ==> l <= m;
    loop invariant \forall integer m; 0 <= m < i ==> l <= m;
    loop invariant \forall integer j; l <= j < n ==> i >= l;
    loop invariant \forall integer j; l <= j < n ==> i <= j;
    loop invariant \forall integer j; l <= j < n ==> 1 <= k;
    loop invariant \forall integer j; l <= j < i ==> i == l;
    loop invariant \forall integer j; l <= j < i ==> (l <= n);
    loop invariant \forall integer j; k <= j < n ==> l <= j < n;
    loop invariant \forall integer j; i <= j < n ==> l <= j;
    loop invariant \forall integer j; 1 <= j <= k ==> l <= i;
    loop invariant \forall integer j; 1 <= j < k ==> l <= i;
    loop invariant \exists integer m; l <= m < n ==> 1 <= k;
    loop invariant \exists integer m; l <= m < i ==> k >= 1;
    loop invariant \exists integer j; l <= j < i ==> 1 <= i;
    loop invariant 0 <= k;
    loop invariant 0 <= i;
    loop invariant 0 < k;
    loop invariant 0 < k || i <= n;
    loop invariant 0 < k || i < n;
    loop invariant 0 < k || 0 <= i;
    loop invariant 0 < i;
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