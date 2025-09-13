

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == \sum integer p, q; 1 <= p < i && 0 <= q < p; (p - q);
  loop invariant k == 1 + \sum(0 <= p < i, \sum(0 <= q < p, (p - q)));
  loop invariant k == 1 + \sum integer m; 1 <= m < i; \sum integer p; 0 <= p < m; (m-p);
  loop invariant j == 0;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i - j <= k;
  loop invariant i * (i - 1) / 2 + 1 <= k;
  loop invariant \forall integer p; 0 <= p < i ==> (\sum integer q; 0 <= q < p; (i-q)) <= k - 1;
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
