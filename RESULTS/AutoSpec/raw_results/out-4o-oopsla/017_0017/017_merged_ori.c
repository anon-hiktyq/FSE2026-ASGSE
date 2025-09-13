

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= j;
 loop invariant 0 <= i;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == i*(i-1)/2 + j*(j-1)/2;
  loop invariant k == i*(i-1)/2 + i;
  loop invariant k == i*(i-1)/2 + 1;
  loop invariant k == i*(i-1)/2 + (i-j)*(j+1)/2;
  loop invariant k == i * (i - 1) / 2 + 1;
  loop invariant k == 1 + \sum(0 <= m < j, (i-m));
  loop invariant k == (i*(i-1))/2 + 1;
  loop invariant k == (i * (i - 1)) / 2;
  loop invariant j <= k;
  loop invariant i*(i-1)/2 <= k;
  loop invariant i <= k;
  loop invariant i * (i - 1) / 2 <= k - 1;
  loop invariant \forall integer m; 0 <= m < j ==> m < i;
  loop invariant \forall integer m; 0 <= m < j ==> k >= i-m;
  loop invariant \forall integer m; 0 <= m < j ==> k >= 1;
  loop invariant \forall integer m; 0 <= m < j ==> k >= (m + i - j + 1);
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i-m);
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m) + 1;
  loop invariant (i*(i-1))/2 <= k;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
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
