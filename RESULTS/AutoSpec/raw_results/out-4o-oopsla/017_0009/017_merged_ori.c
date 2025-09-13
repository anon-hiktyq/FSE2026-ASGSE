

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant k == (j * (2*i-j+1)) / 2 + (i * (i - 1)) / 2 + 1;
 loop invariant k == (i*(i-1))/2 + 1;
 loop invariant k == (i * (i - 1)) / 2 + 1;
 loop invariant j == 0;
 loop invariant j <= i;
 loop invariant i <= n;
 loop invariant i <= k;
 loop invariant i * (i - 1) / 2 + 1 <= k;
 loop invariant \forall integer p; 1 <= p < i ==> k >= (p * (p + 1)) / 2;
 loop invariant \forall integer p; 1 <= p < i ==> (k == ((p * (p - 1)) / 2 + 1)) + \sum_{q=1}^{p-1} (p-q);
 loop invariant \forall integer m; 1 <= m < i ==> k >= (m*(m-1))/2 + 1;
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
  loop invariant k == (i * (i - 1)) / 2 + 1;
  loop invariant k == (i * (i + 1)) / 2;
  loop invariant k - (i*(i-1))/2 == 1;
  loop invariant j <= k;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i*(i-1))/2 <= k;
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
