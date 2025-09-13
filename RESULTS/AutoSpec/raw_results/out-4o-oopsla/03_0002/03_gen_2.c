

/*@
requires l > 0;
requires n > l;
*/
void foo03(int n, int l) {
  int i,k;

  k = 1;
  /*@
  loop invariant 1 <= k <= n;
  loop invariant l <= i <= n;
  loop invariant l < n;
  loop invariant \forall integer m; l <= m < i ==> (1 <= m);
  loop assigns i;
  */
  for (k=1; k<n; k++){
  	i = l;
    /*@
    loop invariant l <= i;
    loop invariant l < n;
    loop invariant k == 1 || (1 <= k < n);
    loop invariant k <= n;
    loop invariant i == n || i == l;
    loop invariant i == l || i > l;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m < i ==> (1 <= m);
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
