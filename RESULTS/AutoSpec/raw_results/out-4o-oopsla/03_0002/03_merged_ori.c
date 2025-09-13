

/*@
requires l > 0;
requires n > l;
*/
void foo03(int n, int l) {
  int i,k;

  k = 1;
  /*@
  loop invariant l <= i;
  loop invariant l < n;
  loop invariant k <= n;
  loop invariant i == l || i == n;
  loop invariant i <= n;
  loop invariant \forall integer m; l <= m < n ==> (1 <= m);
  loop invariant \forall integer m; l <= m < i ==> 1 <= m;
  loop invariant \forall integer m; l <= m < i ==> (1 <= m);
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns i;
  ```c;
  ```;
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
