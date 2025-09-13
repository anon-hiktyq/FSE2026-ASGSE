

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant k == \sum(1 <= t < i, \sum(0 <= u < t, t - u)) + 1;
 loop invariant j == 0;
 loop invariant j <= i;
 loop invariant j < i;
 loop invariant i <= n;
 loop invariant \forall integer p; 1 <= p < i ==> \forall integer q; 0 <= q < p ==> k >= (p - q);
 loop invariant \forall integer p, q; 1 <= p < i && 0 <= q < p ==> k >= (p - q);
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= j;
 loop invariant 0 <= i;
 loop invariant ((i * (i - 1)) / 2) + 1 <= k;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant 1 <= k;
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
