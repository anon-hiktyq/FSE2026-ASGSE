

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant j <= i;
 loop invariant j < i;
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
  loop invariant j <= i;
  loop invariant i - j <= n;
  loop invariant 1 <= k;
  loop invariant j >= 0;
  loop invariant i >= 0;
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m);
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
