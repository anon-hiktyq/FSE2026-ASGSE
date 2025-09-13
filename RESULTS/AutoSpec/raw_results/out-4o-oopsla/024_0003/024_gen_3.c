

void foo024(int n) {
  int i,j,k;
  
  i=0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant 0 <= j <= n;
  loop invariant 0 <= k <= n;
  loop invariant i <= j <= k;
  loop invariant \forall integer x, y; 0 <= x < j && j <= y < k ==> x <= y;
  loop invariant \forall integer p; 0 <= p < j ==> p < n;
  loop assigns i, j, k;
  */
  for (i=0;i<n;i++){

    j=i;
    /*@
    loop invariant k <= n;
    loop invariant j <= n;
    loop invariant j <= k;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant \forall integer x, y; i <= x < j && j <= y < n ==> x <= y;
    loop invariant \forall integer p; i <= p < j ==> p < n;
    loop invariant \forall integer m; i <= m < j ==> m < n;
    loop invariant \forall integer a, b, c; 0 <= a < i && i <= b < n && b <= c < n ==> a <= c;
    loop invariant 0 <= k;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    loop assigns i;
    */
    for (j=i;j<n;j++){

      k=j;
      /*@
      loop invariant k <= n;
      loop invariant k < n;
      loop invariant j <= n;
      loop invariant j <= k;
      loop invariant j < n;
      loop invariant i <= n;
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
