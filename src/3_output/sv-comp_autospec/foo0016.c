
/*@
    requires n > 0;
    */
    
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  /*@
    loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= n);
    loop invariant (0 < \at(n,Pre)) ==> (k == i);
    loop invariant (!(0 < \at(n,Pre))) ==> ((k == 0)&&(i == 0)&&(n == \at(n,Pre)));
    loop invariant n == \at(n,Pre);
    loop assigns i, k;
  */
  while( i < n ) {
	  i++;
	  k++;
  }
            

  int j = 0;
  
  /*@
    loop invariant (0 < \at(n,Pre)) ==> (0 <= j <= n);
    loop invariant (0 < \at(n,Pre)) ==> (k == n - j);
    loop invariant (!(0 < \at(n,Pre))) ==> ((j == 0)&&(k == 0)&&(n == \at(n,Pre)));
    loop invariant n == \at(n,Pre);
    loop assigns j, k;
  */
  while( j < n ) {
    /*@ assert k > 0;*/
    j++;
    k--;
  }
}
