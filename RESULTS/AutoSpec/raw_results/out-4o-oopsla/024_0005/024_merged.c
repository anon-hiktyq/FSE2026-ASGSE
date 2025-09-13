

void foo024(int n) {
  int i,j,k;
  
  i=0;
  for (i=0;i<n;i++){

    j=i;
    /*@
    loop invariant k == j;
    loop invariant j <= n;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant i < n;
    loop invariant \forall integer m; i <= m < j ==> m < n;
    loop invariant \forall integer k; i <= k < j ==> (k >= i && k < n);
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    */
    for (j=i;j<n;j++){

      k=j;
      /*@
      loop invariant k <= n;
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
