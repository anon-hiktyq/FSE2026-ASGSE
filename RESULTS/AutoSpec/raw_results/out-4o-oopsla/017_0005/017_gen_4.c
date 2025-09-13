

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  ```c
  loop invariant 0 <= j <= i;
  loop invariant k == \sum integer m; 1 <= m < i; \sum integer p; 0 <= p < m; (m-p);
  loop invariant k == \sum integer m; 0 <= m < i; m*(m-1)/2;
  loop assigns j;
  loop assigns k;
  ```
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
