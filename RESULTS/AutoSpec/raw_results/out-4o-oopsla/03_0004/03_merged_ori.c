

/*@
requires l > 0;
requires n > l;
*/
void foo03(int n, int l) {
  int i,k;

  k = 1;
  /*@
  loop invariant l == i;
  loop invariant l <= i;
  loop invariant l < n;
  loop invariant k <= n;
  loop invariant i <= n;
  loop invariant \forall integer j; l <= j < n ==> 1 <= j;
  loop invariant \forall integer j; l <= j < i ==> 1 <= j;
  loop invariant \forall integer j; l <= j < i ==> (1 <= j);
  loop invariant \forall integer j; l <= j < i < n ==> 1 <= j;
  loop invariant \forall integer j; 1 <= j < k ==> l == i;
  loop invariant \forall integer j; 1 <= j < k ==> l <= n;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  */
  for (k=1; k<n; k++){
  	i = l;
    /*@
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant i == n || (l <= i < n);
    loop invariant i == l;
    loop invariant i <= n;
    loop invariant \forall integer j; l <= j < i ==> 1 <= j;
    loop invariant \forall integer j; l <= j < i ==> (1 <= j);
    loop invariant 1 <= k;
    loop assigns i;
    */
    for (; i<n; i++) {
    }

    }
  
    // @ assert \forall integer i; (l <= i < n) ==> (1 <= i); 
  

}
