

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant m < i, (i - m));
  loop invariant k == (i * (i - 1)) / 2 + 1;
  loop invariant k == (i * (i + 1)) / 2;
  loop invariant k - (i*(i-1))/2 == 1;
  loop invariant j <= k;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant \sum(0 <= m;
  loop invariant \sum(0 <= k;
  loop invariant \forall integer m; 0 <= m < j ==> k == \sum(integer l = 1, l < i, (i-l));
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i*(i-1))/2 <= k;
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
