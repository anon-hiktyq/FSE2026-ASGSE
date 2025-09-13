

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant k == (i * (i - 1)) / 2 + 1;
 loop invariant j <= i;
 loop invariant i <= n;
 loop invariant j >= 0;
 loop invariant 1 <= k;
 loop invariant k >= (i * (i - 1)) / 2;
 loop invariant \forall integer x; 0 <= x < j ==> k >= i - x;
 loop invariant \forall integer x; 0 <= x < j ==> k >= (i * (i - 1)) / 2 + 1;
 loop invariant j <= i;
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= j;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == (i * (i - 1)) / 2 + 1;
  loop invariant j <= k;
  loop invariant j <= i;
  loop invariant j <= i && i <= n;
  loop invariant j * (j - 1) / 2 <= k;
  loop invariant j * (i - 1) + (i * (i - 1) / 2) <= k;
  loop invariant i > 0 && 0 <= j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant i * (i - 1) / 2 <= k;
  loop invariant \forall integer x; 0 <= x < j ==> k >= i - x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i * (i - 1)) / 2 <= k;
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
