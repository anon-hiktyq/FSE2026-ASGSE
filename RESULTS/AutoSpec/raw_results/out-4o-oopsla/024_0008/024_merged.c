

void foo024(int n) {
  int i,j,k;
  
  i=0;
  for (i=0;i<n;i++){

    j=i;
    /*@
    loop invariant k <= n;
    loop invariant j <= n;
    loop invariant j <= k;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant i < n;
    loop invariant i < n+1;
    loop invariant \forall integer x, y; i <= x < j <= n ==> x <= y;
    loop invariant \forall integer p, q, r; (0 <= i <= p) && (p <= q <= j) && (q <= r < n) ==> r >= i;
    loop invariant 0 <= k;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    */
    for (j=i;j<n;j++){

      k=j;
      /*@
      loop invariant k <= n;
      loop invariant k < n + 1;
      loop invariant j <= n;
      loop invariant j <= k;
      loop invariant j < n;
      loop invariant i <= k;
      loop invariant i <= j;
      loop invariant i < n;
      loop invariant 0 <= k;
      loop invariant 0 <= j;
      loop invariant 0 <= i;
      loop assigns k;
      */
      for (k=j;k<n;k++){
	       // @assert k >= i;
      }
    }
  }
}
