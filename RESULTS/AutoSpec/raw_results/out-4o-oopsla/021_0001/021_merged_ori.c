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
  loop invariant k == i * (v == 0 ? c1 : c2);
  loop invariant k <= i * c1;
  loop invariant k <= i * 4000;
  loop invariant i <= n;
  loop invariant i * c2 <= k;
  loop invariant i * c1 / 2 <= k;
  loop invariant i * 2000 <= k;
  loop invariant \exists integer m; 0 <= m <= i && k == m * c1 + (i - m) * c2;
  loop invariant 0 <= i;
  loop invariant 0 < k;
  loop assigns v;
  loop assigns k;
  loop assigns i;
  loop assigns \nothing;
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

