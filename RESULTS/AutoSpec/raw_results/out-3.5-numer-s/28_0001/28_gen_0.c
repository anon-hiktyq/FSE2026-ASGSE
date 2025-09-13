/*@
  requires a >= 1;
  requires b >= 1;
*/
void hoo28(int a,int b) { 
    int x,y,u,v;
  
    //pre-condition
    x=a;
    y=b;
    u=b;
    v=0;
    
  
    //loop-body
    /*@
    Looking at this code, I need to generate loop invariants that maintain the relationship `x*u + y*v == a*b` throughout the loop execution.
    
    ```c
    loop invariant x*u + y*v == a*b;
    loop invariant x >= 0;
    loop invariant y >= 1;
    loop invariant u == b;
    loop invariant v >= 0;
    loop assigns x;
    loop assigns v;
    ```
    */
    while(x>y) {
      x=x-y;
      v=v+u;
    }
  
    //post-condition
    /*@ assert x*u + y*v == a*b; */
  }   