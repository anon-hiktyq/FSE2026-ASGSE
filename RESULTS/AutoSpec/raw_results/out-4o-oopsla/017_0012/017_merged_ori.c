

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == \sum{int p; 1 <= p < i}( \sum{int q; 0 <= q < p}( p - q ));
  loop invariant k == \sum(1 <= p < i, \sum(0 <= q < p, (p - q))) + 1;
  loop invariant k == 1 + \sum(1 <= x < i, \sum(0 <= y < x, (x - y)));
  loop invariant k == 1 + \sum(1 <= p < i, \sum(0 <= q < p, p - q));
  loop invariant k == 1 + \sum(0 <= x < i, \sum(0 <= y < x, x - y));
  loop invariant k == 1 + \sum(0 <= p < i, \sum(0 <= q < p, p-q));
  loop invariant k == (\sum integer p, q; 1 <= p < i && 0 <= q < p; (p - q)) + 1;
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
