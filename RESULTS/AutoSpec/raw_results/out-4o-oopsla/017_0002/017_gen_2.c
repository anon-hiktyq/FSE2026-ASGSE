

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant 1 <= i <= n;
 loop invariant 1 <= k;
 loop invariant i <= n;
 loop invariant (i * (i - 1)) / 2 + 1 <= k;
 loop invariant k == 1 + \sum(1 <= m < i, m * (m - 1) / 2);
 loop assigns i;
 loop assigns k;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j == 0;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i - j <= k;
  loop invariant i * (i - 1) / 2 + 1 <= k;
  loop invariant 1 <= k;
  loop invariant 1 + (i * (i - 1)) / 2 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i*(i-1))/2 + 1 <= k;
  loop invariant (i * (i - 1)) / 2 <= k;
  loop invariant (i * (i - 1)) / 2 + 1 <= k;
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
