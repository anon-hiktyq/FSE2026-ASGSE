

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant 0 <= j <= i <= n;
  loop invariant k == 1 + \sum(0 <= p < i, \sum(0 <= q < p, (p - q)));
  loop invariant k >= (i * (i - 1)) / 2 + 1;
  loop assigns j;
  loop assigns k;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
