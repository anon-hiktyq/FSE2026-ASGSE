
void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
   requires n >= 1;
   requires j == 0;
   requires i == 1;
   requires k == 1;
   ensures k >= n;
 */
 
 /* >>> LOOP INVARIANT TO FILL <<< */
 
 /*@
   loop invariant (1 < \at(n,Pre)) ==> (k >= n*(n-1)/2 + 1);
   loop invariant (1 < \at(n,Pre)) ==> (1 <= i && i < n);
   loop invariant (1 < \at(n,Pre)) ==> (((j == 0)&&(i == 1)&&(k == 1)&&(n == \at(n,Pre))) || (j < i));
   loop invariant !(1 < \at(n,Pre)) ==> ((j == 0)&&(i == 1)&&(k == 1)&&(n == \at(n,Pre)));
   loop invariant n == \at(n,Pre);
   loop assigns j, k, i;
 */
 while(i < n) {
  j = 0;
  
  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant 0 <= j <= i;
    loop invariant \forall integer m; 0 <= m < i ==> k >= m + 1;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  
  i++;
 }
 
 /*@ assert k >= n */;
 
}
