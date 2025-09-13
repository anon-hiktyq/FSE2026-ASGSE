

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant k == 1 + \sum(1 <= m < i, m * (m - 1) / 2);
 loop invariant k == 1 + \sum integer p; 1 <= p < i ==> p*(p-1)/2;
 loop invariant k == 1 + \sum integer m; 1 <= m < i; m * (m + 1) / 2;
 loop invariant j <= i;
 loop invariant i <= n;
 loop invariant i <= k;
 loop invariant i * (i - 1) <= 2 * k - 2;
 loop invariant i * (i - 1) / 2 + 1 <= k;
 loop invariant \forall integer l; 0 <= l < i ==> (i * (i - 1)) / 2 + 1 <= k;
 loop invariant 1; <= k;
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= k;
 loop invariant 0 <= j;
 loop invariant (i*(i-1))/2 + 1 <= k;
 loop invariant (i * (i - 1)) / 2 <= k;
 loop invariant (i * (i - 1)) / 2 + 1 <= k;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 ```c;
 ```;
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
