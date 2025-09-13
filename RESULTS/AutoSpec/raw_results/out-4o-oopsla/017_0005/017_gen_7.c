

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant 0 <= j <= i;
  loop invariant k >= 1 + (i * (i - 1)) / 2;
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
