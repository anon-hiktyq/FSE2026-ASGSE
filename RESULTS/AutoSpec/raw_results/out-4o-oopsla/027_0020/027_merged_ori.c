
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer m; l <= m <= n ==> (m >= l);
  loop invariant \forall integer m; l <= m < n ==> m >= l;
  loop invariant \forall integer m; l <= m < n ==> (m >= l);
  loop invariant \forall integer j; l <= j < n ==> k >= 1;
  loop invariant \forall integer j; l <= j < n ==> 1 <= k;
  loop invariant \forall integer j; l <= j < n ==> 0 < l;
  loop invariant \forall integer j; l <= j < n ==> 0 < k;
  loop invariant \forall integer j; l <= j < n ==> (j >= l);
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; l <= j < k ==> 1 <= k;
  loop invariant \forall integer j; l <= j < i ==> 1 <= k;
  loop invariant \forall integer j; l <= j < i ==> (1 <= k);
  loop invariant \forall integer j; k <= j < n ==> (1 <= k);
  loop invariant \forall integer j; i <= j < n ==> (1 <= k);
  loop invariant \forall integer j; 0 <= j < k ==> (1 <= k);
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l > 0 && i >= l;
    loop invariant l <= n;
    loop invariant l < n;
    loop invariant k < n ==> i >= l;
    loop invariant i <= n;
    loop invariant i <= n;
    loop invariant i <= n || l < n;
    loop invariant i <= n || i < n;
    loop invariant i <= n || 1 <= k + n - i;
    loop invariant i <= n || 0 < l;
    loop invariant i < n;
    loop invariant i < n;
    loop invariant i < n || l < n;
    loop invariant i < n || 1 <= k + n - i;
    loop invariant \forall integer m; l <= m < i ==> m >= l;
    loop invariant \forall integer j; l <= j <= i ==> j >= l;
    loop invariant \forall integer j; l <= j < i ==> l <= j;
    loop invariant \forall integer j; l <= j < i ==> j >= l;
    loop invariant \forall integer j; l <= j < i ==> (m >= l);
    loop invariant \forall integer j; k <= j < n ==> (1 <= k);
    loop invariant \forall integer j; i <= j < n ==> j >= l;
    loop invariant \forall integer j; i <= j < n ==> 1 <= k;
    loop invariant \forall integer j; 0 <= j < n ==> j >= l;
    loop invariant 1 <= k + n - i;
    loop invariant 1 <= k + n - i || l < n;
    loop invariant 1 < k + n - i;
    loop invariant 0 <= l;;
    loop invariant 0 < l;;
    loop invariant 0 < l || l < n;
    loop invariant 0 < l || i < n;
    loop invariant 0 < l || 1 <= k + n - i;
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant \forall integer m; l <= m < n ==> (m >= l);
    loop invariant \forall integer j; l <= j < i ==> 1 <= k;
    loop invariant \forall integer j; l <= j < i ==> (1 <= k);
    loop invariant \forall integer j; i <= j < n ==> (1 <= k);
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }

    // @ assert \forall i; (l <= i < n) ==> (1 <= k);
  }

}