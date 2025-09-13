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
  loop invariant k >= c2 * i;
  loop invariant k <= c1 * i;
  loop invariant k == (c1 * (i - \sum_{j=0}^{i-1} (unknown2() % 2 != 0))) + (c2 * \sum_{j=0}^{i-1} (unknown2() % 2 != 0));
  loop assigns i;
  loop assigns v;
  loop assigns k;
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

