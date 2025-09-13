

void foo024(int n) {
  int i,j,k;
  
  i=0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant \forall integer x; 0 <= x < i ==> x < n;
  loop invariant \forall integer a; 0 <= a < i ==> a <= n;
  loop assigns i;
  */
  for (i=0;i<n;i++){

    j=i;
    /*@
    loop invariant j <= n;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant i < n;
    loop invariant \forall integer x; i <= x < j ==> x <= n;
    loop invariant \forall integer m; i <= m < j ==> m < n;
    loop invariant \forall integer l; i <= l < j ==> l < n;
    loop invariant \forall integer k; i <= k < j ==> k <= n;
    loop invariant \forall integer k; i <= k < j ==> k < n;
    loop invariant \forall integer a; i <= a < j ==> a <= n;
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
