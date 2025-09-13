/*@
  requires n > 0;
*/
void hoo25(int n,int a) { 
    
    int i = 0;
    int sn = 0;

    /*@
    loop invariant sn == i * a;
    loop invariant i <= n;
    loop invariant 0 <= i;
    loop assigns sn;
    loop assigns i;
    ```c;
    ```;
    Looking at this code, I need to generate loop invariants for the while loop that accumulates `sn` by adding `a` in each iteration.;
    */
    while(i < n) {
      sn = sn + a;
      i++;
    }
  
    /*@ assert sn == n*a || sn == 0; */
  }