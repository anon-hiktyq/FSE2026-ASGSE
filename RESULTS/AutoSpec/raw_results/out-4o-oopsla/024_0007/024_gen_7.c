

void foo024(int n) {
  int i,j,k;
  
  i=0;
  for (i=0;i<n;i++){

    j=i;
    for (j=i;j<n;j++){

      k=j;
      /*@
      ```c
      loop invariant i <= j <= k <= n;
      loop invariant 0 <= i < n;
      loop invariant 0 <= j < n;
      loop invariant 0 <= k <= n;
      loop invariant k >= i;
      loop assigns k;
      ```
      */
      for (k=j;k<n;k++){
	       // @assert k >= i;
      }
    }
  }
}
