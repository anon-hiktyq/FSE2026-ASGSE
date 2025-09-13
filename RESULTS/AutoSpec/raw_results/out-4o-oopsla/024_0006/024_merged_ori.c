

void foo024(int n) {
  int i,j,k;
  
  i=0;
  /*@
  loop invariant k <= n;
  loop invariant j <= n;
  loop invariant j <= k;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant i <= j;
  loop invariant \forall integer x, y, z; 0 <= x <= i && i <= y <= j && j <= z < n ==> (x <= y && y <= z);
  loop invariant \forall integer p, q, r; 0 <= p <= i && i <= q <= j && j <= r <= k ==> p <= q <= r;
  loop invariant \forall integer m; j <= m < k ==> m < n;
  loop invariant \forall integer m; i <= m < j ==> m < n;
  loop invariant \forall integer m; 0 <= m < i ==> m >= 0;
  loop invariant \forall integer m; 0 <= m < i ==> m < n;
  loop invariant \forall integer m; 0 <= m < i ==> \forall integer p; m <= p < n ==> p >= m;
  loop invariant \forall integer k; i <= k < n ==> (k >= i && k < n);
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  loop assigns i;
  ```c;
  ```;
  */
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
