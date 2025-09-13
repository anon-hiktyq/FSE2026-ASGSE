int unknown();
/*@
requires n > 0;
requires n < 10;
*/
void foo021(int n,int j,int v) {
  int c1 = 4000;
  int c2 = 2000;
  int i = 0;
  int k = 0;
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant k == i * c1 || k == (i-1) * c1 + c2;
  loop invariant i > 0 ==> k >= c2;
  loop invariant i == n ==> k > n;
  loop assigns i, k, v;
  */
  while( i < n ) {
    i++;
    if(unknown2() % 2 == 0) {
        v = 0;
    }
    else v = 1;
    
    if( v == 0 ){
      k += c1;
    }else {
      k += c2;
    }
  }
  
  // @ assert k > n;
}

