

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 while(i < n) {
  j = 0;
  /*@
  ```c
    /*@
      loop invariant 0 <= j <= i;
      loop invariant k == \sum(0 <= p < j, (i - p)) + \sum(0 <= q < i, (i - q));
      loop assigns j, k;
    */
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
