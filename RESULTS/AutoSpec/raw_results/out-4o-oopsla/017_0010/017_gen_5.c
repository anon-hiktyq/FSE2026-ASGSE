

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant j <= i;
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= j;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j <= i;
  loop invariant k >= i * (i - 1) / 2;
  loop invariant 0 <= j <= i;
  loop invariant i <= n;
  loop invariant k == \sum(0 <= t < j, i - t) + 1;
  loop invariant j * (j - 1) / 2 <= k;
  loop invariant j <= k;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
