

void foo024(int n) {
  int i,j,k;
  
  i=0;
  for (i=0;i<n;i++){

    j=i;
    for (j=i;j<n;j++){

      k=j;
      /*@
      loop invariant 0 <= k <= n;
      loop invariant j <= k;
      loop invariant i <= j;
      loop invariant i <= k;
      loop invariant j < n ==> k >= j;
      loop assigns k;
      */
      for (k=j;k<n;k++){
	       // @assert k >= i;
      }
    }
  }
}
