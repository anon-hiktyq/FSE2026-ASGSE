
/*@
requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;
 

  k = 1;
  /*@
  loop invariant l <= n;
  loop invariant l <= i;
  loop invariant k <= n;
  loop invariant i == l;
  loop invariant i <= n;
  loop invariant \forall integer j; l <= j < n ==> k < n;
  loop invariant \forall integer j; l <= j < n ==> 1 <= k;
  loop invariant \forall integer j; l <= j < n ==> 1 <= j;
  loop invariant \forall integer j; l <= j < n ==> 1 < k;
  loop invariant \forall integer j; l <= j < n ==> (1 <= k);
  loop invariant \forall integer j; l <= j < i ==> l < i;
  loop invariant \forall integer j; l <= j < i ==> k >= 1;
  loop invariant \forall integer j; l <= j < i ==> 1 <= k;
  loop invariant \forall integer j; l <= j < i ==> (1 <= k);
  loop invariant \forall integer j; l <= j < i ==> (1 <= j <= k);
  loop invariant \forall integer j; 1 <= j < k ==> l <= i < n;
  loop invariant \forall integer j; 1 <= j < k ==> l < i;
  loop invariant \forall integer j; 1 <= j < k ==> k >= l;
  loop invariant \forall integer j; 1 <= j < k ==> k >= 1;
  loop invariant \forall integer j; 1 <= j < k ==> k == j + 1;
  loop invariant \forall integer j; 1 <= j < k ==> \forall integer i; l <= i < n ==> (k < n);
  loop invariant \forall integer j; 1 <= j < k ==> 1 <= k;
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= j);
  loop invariant \forall integer j; 0 <= j < k ==> l <= n;
  loop invariant \forall integer j; 0 <= j < k ==> k <= n;
  loop invariant \forall integer j; 0 <= j < k ==> 1 <= k;
  loop invariant \forall integer j; 0 < j < k ==> 1 <= k;
  loop invariant \forall integer j; 0 < j < k ==> 0 < l;
  loop invariant \forall integer j; 0 < j < k ==> (1 <= k);
  loop invariant 1 < n;
  loop invariant \forall integer j; 1 <= j < k ==> \forall integer i; l <= i < n ==> (1 <= j);
  loop invariant \forall integer j; 1 <= j < k ==> (1 <= k);
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k = 1; k < n; k++) {
    i = l;
    /*@
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant i < n;
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