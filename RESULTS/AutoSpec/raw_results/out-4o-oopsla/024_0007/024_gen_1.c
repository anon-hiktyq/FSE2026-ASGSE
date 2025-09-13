

void foo024(int n) {
  int i,j,k;
  
  i=0;
  for (i=0;i<n;i++){

    j=i;
    for (j=i;j<n;j++){

      k=j;
      /*@
      ```c
            /*@ 
              loop invariant i <= j <= k <= n;
              loop invariant i <= k < n + 1;
              loop assigns k;
            */
      ```
      */
      for (k=j;k<n;k++){
	       // @assert k >= i;
      }
    }
  }
}
