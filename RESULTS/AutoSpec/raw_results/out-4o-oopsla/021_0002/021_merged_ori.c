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
  loop invariant v == 0 || v == 1;
  loop invariant k == i * c1 || k == i * c2 || k == i * (c1 + c2) / 2;
  loop invariant k == i * c1 || k == i * c2 || k == i * ((c1 + c2) / 2);
  loop invariant k == i * c1 || k == i * c2 || (c1 < c2 && k >= i * c2);
  loop invariant k == i * c1 || k == (i-1) * c1 + c2;
  loop invariant k == i * c1 || k == (i - j) * c1 + j * c2;
  loop invariant k == i * (v == 0 ? c1 : c2);
  loop invariant k <= i * c1;
  loop invariant k <= c1 * i;
  loop invariant i > 0 ==> k >= c2;
  loop invariant i == n ==> k > n;
  loop invariant i <= n;
  loop invariant i <= n && k >= i * c2;
  loop invariant i < n ==> k > i * c2;
  loop invariant i * c2; <= k;
  loop invariant i * c2 <= k;
  loop invariant c2 * i <= k;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop invariant (v == 0 || v == 1);
  loop assigns v;
  loop assigns k;
  loop assigns i;
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

