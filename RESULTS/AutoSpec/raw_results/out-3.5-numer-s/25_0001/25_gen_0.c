/*@
  requires n > 0;
*/
void hoo25(int n,int a) { 
    
    int i = 0;
    int sn = 0;

    /*@
    Looking at this code, I need to generate loop invariants for the while loop that accumulates `sn` by adding `a` in each iteration.
    
    ```c
    loop invariant 0 <= i <= n;
    loop invariant sn == i * a;
    loop assigns i;
    loop assigns sn;
    ```
    */
    while(i < n) {
      sn = sn + a;
      i++;
    }
  
    /*@ assert sn == n*a || sn == 0; */
  }