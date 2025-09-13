

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant k == i * (i - 1) / 2 + j * (j + 1) / 2;
 loop invariant k == (i*(i-1))/2;
 loop invariant k == (i * (i - 1)) / 2 + j;
 loop invariant k == (i * (i - 1)) / 2 + j * (j - 1) / 2;
 loop invariant k == (i * (i - 1)) / 2 + 1;
 loop invariant k <= i * (i - 1) / 2 + (i - 1);
 loop invariant k <= i * (i + 1) / 2;
 loop invariant j == 0;;
 loop invariant j <= k;
 loop invariant j <= i;
 loop invariant j < i;;
 loop invariant j < i;
 loop invariant i*(i-1)/2 <= k;
 loop invariant i <= n;
 loop invariant i <= k;
 loop invariant i < n;
 loop invariant i * (i - 1) / 2 <= k;
 loop invariant i * (i - 1) / 2 <= k - 1;
 loop invariant \forall integer m; 0 <= m < n ==> m <= i;
 loop invariant \forall integer m; 0 <= m < j ==> k >= i - m + 1;
 loop invariant \forall integer m; 0 <= m < j ==> k >= 1;
 loop invariant \forall integer m; 0 <= m < j ==> k >= (i-m);;
 loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m);
 loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m) + 1;
 loop invariant \forall integer m; 0 <= m < j ==> (k - m) >= 1;
 loop invariant \forall integer m; 0 <= m < j ==> (i * (i - 1)) / 2 <= k;
 loop invariant \forall integer m; 0 <= m < i ==> k >= (i*(i-1))/2 + m*(m+1)/2;
 loop invariant \forall integer m; 0 <= m < i ==> k >= (i * (i - 1) / 2 + 1);
 loop invariant 1 <= i - j;
 loop invariant 0; < i;
 loop invariant (i*(i-1))/2 <= k;
 loop invariant (i - 1) * i / 2 <= k - j * (j - 1) / 2;
 loop invariant (i * (i - 1)) / 2 <= k;
 loop invariant (i * (i - 1)) / 2 < k;
 loop invariant (i * (i - 1)) / 2 + j == k - 1;
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
  loop invariant k == (i*(i-1))/2 + 1;
  loop invariant k == (i * (i - 1)) / 2;
  loop invariant j <= k;
  loop invariant j <= i;
  loop invariant i*(i-1)/2 <= k;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant i * (i - 1) / 2 <= k - 1;
  loop invariant \forall integer m; 0 <= m < j ==> m < i;
  loop invariant \forall integer m; 0 <= m < j ==> k >= i-m;
  loop invariant \forall integer m; 0 <= m < j ==> k >= 1;
  loop invariant \forall integer m; 0 <= m < j ==> k >= (m + i - j + 1);
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i-m);
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m) + 1;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i*(i-1))/2 <= k;
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
