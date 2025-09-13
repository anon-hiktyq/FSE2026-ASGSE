

void foo024(int n) {
  int i,j,k;
  
  i=0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant \forall integer m; 0 <= m < i ==> \forall integer j; i <= j < n ==> j >= m;
  loop assigns i;
  */
  for (i=0;i<n;i++){

    j=i;
    /*@
    loop invariant j <= n;
    loop invariant j < n;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant i < n;
    loop invariant \forall integer m; i <= m < j ==> m >= i;
    loop invariant \forall integer m; i <= m < j ==> m <= n;
    loop invariant \forall integer m; i <= m < j ==> m < n;
    loop invariant \forall integer m; i <= m < j ==> j <= n;
    loop invariant \forall integer l; i <= l < j ==> l <= j;
    loop invariant \forall integer l; i <= l < j ==> i <= l;
    loop invariant \forall integer l, m; i <= l < j <= m < n ==> k >= j;
    loop invariant \forall integer a, b; 0 <= a <= i && i <= b < n ==> a <= b;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    */
    for (j=i;j<n;j++){

      k=j;
      /*@
      loop invariant k <= n;
      loop invariant j <= n;
      loop invariant j <= k;
      loop invariant j < n;
      loop invariant j < n ==> k >= j;
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
