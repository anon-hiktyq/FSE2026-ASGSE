

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant 0 <= j <= i;
  loop invariant k >= i;
  loop invariant k == \sum(1 <= p < i, \sum(0 <= q < p, (p - q))) + 1;
  loop assigns i, j, k;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
