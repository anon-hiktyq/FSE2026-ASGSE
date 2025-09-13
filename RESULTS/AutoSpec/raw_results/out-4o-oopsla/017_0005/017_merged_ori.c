

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  loop invariant k == \sum integer m; 1 <= m < i; \sum integer p; 0 <= p < m; (m-p);
  loop invariant k == \sum integer m; 0 <= m < i; m*(m-1)/2;
  loop invariant k == \sum integer a, b; 1 <= a < i && 0 <= b < a; (a - b);
  loop invariant k == 1 + i*(i-1)/2;
  loop invariant k == (i*(i-1))/2 + 1;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant \forall integer x, y; 0 <= x < i && 0 <= y < x ==> (k >= (x * (x + 1)) / 2);
  loop invariant \forall integer m; 0 <= m < i ==> k >= (i * (i - 1)) / 2 + m;;
  loop invariant 1 + (i * (i - 1)) / 2 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i * (i - 1)) / 2 <= k;
  loop invariant ((i - 1) * i) / 2 + 1 <= k;
  loop assigns k;
  loop assigns j;
  ```c;
  ```;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
