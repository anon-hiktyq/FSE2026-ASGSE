

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant 0 < i <= n;
 loop invariant k == 1 + i*(i-1)/2;
 loop invariant (i-1)*(i-2)/2 + 1 <= k;
 loop invariant \forall integer x, y; 0 <= x < i && 0 <= y < x ==> (k >= (x * (x + 1)) / 2);
 loop invariant i <= k;
 loop assigns i;
 loop assigns k;
 loop invariant 0 <= j <= i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == 1 + i*(i-1)/2;
  loop invariant k == (i*(i-1))/2 + 1;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant \forall integer x, y; 0 <= x < i && 0 <= y < x ==> (k >= (x * (x + 1)) / 2);
  loop invariant 1 + (i * (i - 1)) / 2 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i * (i - 1)) / 2 <= k;
  loop invariant ((i - 1) * i) / 2 + 1 <= k;
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
