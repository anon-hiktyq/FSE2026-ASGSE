
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant \forall integer j; l <= j < n ==> 1 <= k;
  loop invariant \forall integer j; l <= j < n ==> 1 <= j;
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; l <= j < i ==> l < i;
  loop invariant \forall integer j; l <= j < i ==> k >= 1;
  loop invariant \forall integer j; l <= j < i ==> 1 <= k;
  loop invariant \forall integer j; l <= j < i ==> (1 <= k);
  loop invariant \forall integer j; 1 <= j < k ==> k >= 1;
  loop invariant \forall integer j; 1 <= j < k ==> \forall integer i; l <= i < n ==> (1 <= j);
  loop invariant \forall integer j; 1 <= j < k ==> 1 <= k;
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= k);
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= j);
  loop invariant \forall integer j; 0 <= j < k ==> 1 <= k;
  loop invariant \forall integer j; 0 < j < k ==> 1 <= k;
  loop invariant \forall integer j; 0 < j < k ==> 0 < l;
  loop invariant \forall integer j; 0 < j < k ==> (1 <= k);
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l == i ==> l < n;
    loop invariant l == i ==> 1 <= k;
    loop invariant l <= n;
    loop invariant l <= n || k <= n;
    loop invariant l <= n || i <= n;
    loop invariant l <= n || i < n;
    loop invariant l <= n || 1 <= i;
    loop invariant l <= n || 0 <= n;
    loop invariant l <= n || 0 < n;
    loop invariant l <= n || 0 < l;
    loop invariant l < n;
    loop invariant k <= n;
    loop invariant k <= n || i <= n;
    loop invariant k <= n || i < n;
    loop invariant k <= n || 1 <= i;
    loop invariant k <= n || 0 <= n;
    loop invariant k <= n || 0 < n;
    loop invariant i <= n;
    loop invariant i <= n;
    loop invariant i < n;
    loop invariant i < n;
    loop invariant i < n || i <= n;
    loop invariant \forall integer m; l <= m < n ==> l <= i <= m;
    loop invariant \forall integer m; l <= m < n ==> 1 <= k + m;
    loop invariant \forall integer m; l <= m < n ==> 0 < l;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant \forall integer m; l <= m < i ==> (1 <= m);
    loop invariant \forall integer m; k <= m < n ==> 1 <= k;
    loop invariant \forall integer j; l <= j < n ==> 1 <= i;
    loop invariant \forall integer j; l <= j < i ==> n >= i;
    loop invariant \forall integer j; l <= j < i ==> l <= i;
    loop invariant \forall integer j; l <= j < i ==> l < n;
    loop invariant \forall integer j; l <= j < i ==> k >= 1;
    loop invariant \forall integer j; l <= j < i ==> k > 0;
    loop invariant \forall integer j; l <= j < i ==> j <= n;
    loop invariant \forall integer j; l <= j < i ==> i >= l;
    loop invariant \forall integer j; l <= j < i && 1 <= k;
    loop invariant \forall integer j; k <= j < n ==> 1 <= k;
    loop invariant \forall integer j; 0 <= j < k ==> l <= n;
    loop invariant \forall integer j; 0 <= j < k ==> 1 <= i;
    loop invariant 1 <= i;
    loop invariant 1 <= i || i <= n;
    loop invariant 1 <= i || i < n;
    loop invariant 1 <= i || 0 < n;
    loop invariant 1 < i;
    loop invariant 0 <= n;
    loop invariant 0 <= n;
    loop invariant 0 <= n || i <= n;
    loop invariant 0 <= n || i < n;
    loop invariant 0 <= n || 1 <= i;
    loop invariant 0 <= n || 0 < n;
    loop invariant 0 <= l;;
    loop invariant 0 < n;
    loop invariant 0 < n;
    loop invariant 0 < n || i <= n;
    loop invariant 0 < n || i < n;
    loop invariant 0 < l;;
    loop invariant 0 < l || k <= n;
    loop invariant 0 < l || i <= n;
    loop invariant 0 < l || i < n;
    loop invariant 0 < l || 1 <= i;
    loop invariant 0 < l || 0 <= n;
    loop invariant 0 < l || 0 < n;
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant \forall integer j; l <= j < n ==> 1 <= k;
    loop invariant \forall integer j; l <= j < i ==> 1 <= k;
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