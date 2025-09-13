/*@
  requires n > 0;
*/
void hoo25(int n,int a) { 
    
    int i = 0;
    int sn = 0;

    /*@
    loop invariant 0 <= i <= n;
    loop invariant sn == i * a;
    loop invariant sn == 0 || sn == i * a;
    loop assigns i, sn;
    */
    while(i < n) {
      sn = sn + a;
      i++;
    }
  
    /*@ assert sn == n*a || sn == 0; */
  }