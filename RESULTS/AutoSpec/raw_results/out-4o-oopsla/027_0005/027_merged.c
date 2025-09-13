
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer m; l <= m < k ==> (1 <= k);
  loop invariant \forall integer j; l <= j <= i ==> (k >= 1);
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; l <= j < k ==> (0 <= l < n);
  loop invariant \forall integer j; l <= j < i ==> (1 <= i);
  loop invariant \forall integer j; 1 <= j < k ==> j <= n;
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= k);
  loop invariant \forall integer j; 0 <= j < k ==> (1 <= k);
  loop invariant \exists integer j; 0 <= j <= k && k == j;
  loop invariant 1 <= k;
  loop invariant 0 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l <= n;
    loop invariant l < n;
    loop invariant l < n || 0 < k;
    loop invariant k <= n;
    loop invariant k <= n || l < n;
    loop invariant k <= n || i <= n;
    loop invariant k <= n || 0 < k;
    loop invariant i <= n;
    loop invariant i <= n || l < n;
    loop invariant i <= n || 0 < k;
    loop invariant i < n;
    loop invariant \forall integer m; l <= m <= i ==> k < n;
    loop invariant \forall integer m; l <= m < n ==> (1 <= k);
    loop invariant \forall integer m; l <= m < i ==> m >= l;
    loop invariant \forall integer m; l <= m < i ==> 1 <= k;
    loop invariant \forall integer m; l <= m < i ==> (l <= i);
    loop invariant \forall integer m; l <= m < i ==> (1 <= i);
    loop invariant \forall integer m; 0 <= m < k ==> l <= i;
    loop invariant \forall integer m; 0 <= m < k ==> (l <= i);
    loop invariant \forall integer m; 0 <= m < k ==> (1 <= k);
    loop invariant \forall integer j; l <= j <= i ==> k >= 1;
    loop invariant \forall integer j; l <= j < n ==> k < n+1;
    loop invariant \forall integer j; l <= j < k ==> (0 <= l < n);
    loop invariant \forall integer j; l <= j < i ==> 1 <= k;
    loop invariant \forall integer j; l <= j < i ==> (l <= i);
    loop invariant \forall integer j; l <= j < i ==> (k < n);
    loop invariant \forall integer j; i <= j < n ==> 1 <= k;
    loop invariant \forall integer j; 0 <= j < k ==> (1 <= k && l <= i && i <= n);
    loop invariant \forall integer j; 0 <= j < k ==> (1 <= j);
    loop invariant \forall integer j; 0 <= j < i ==> l <= i;
    loop invariant \forall integer j; 0 <= j < i ==> (l <= i);
    loop invariant \exists integer m; l <= m <= i && m == l;
    loop invariant \exists integer j; 0 <= j <= i && i == j;
    loop invariant 0 <= k;
    loop invariant 0 < k;
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant \forall integer m; l <= m < n ==> (k < n);
    loop invariant \forall integer m; l <= m < i ==> (1 <= k);
    loop invariant \forall integer m; 0 <= m < k ==> (l <= i && 1 <= k);
    loop invariant \forall integer j; l <= j < i ==> (1 <= k);
    loop invariant \forall integer j; l <= j < i ==> (1 <= i);
    loop invariant \forall integer j; i <= j < n ==> (1 <= k);
    loop invariant \forall integer j; 1 <= j <= i ==> (1 <= k);
    loop invariant 1 <= k;
    loop invariant 0 <= i;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}