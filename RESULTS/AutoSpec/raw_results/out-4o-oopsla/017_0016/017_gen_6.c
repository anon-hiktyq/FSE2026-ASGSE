

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant 1 <= i <= n;
 loop invariant 1 <= k;
 loop invariant 0 <= j;
 loop invariant k == 1 + \sum(1 <= p < i, \sum(0 <= q < p, p - q));
 loop assigns i, j, k;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
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
