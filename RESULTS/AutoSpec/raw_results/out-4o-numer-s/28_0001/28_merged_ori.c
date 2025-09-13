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
    loop invariant y <= x;
    loop invariant x*u + y*v == a*b;
    loop invariant x >= 1 && y >= 1;
    loop invariant x >= 0 && y >= 1;
    loop invariant x * u + y * v == a * b;
    loop invariant v == (a - x) * b / y;
    loop invariant v % u == 0;
    loop invariant u == b;
    loop invariant 1 <= y;
    loop invariant 1 <= x;
    loop invariant 0 <= x;
    loop invariant 0 <= v;
    loop invariant 0 < y;
    loop assigns x;
    loop assigns v;
    */
    while(x>y) {
      x=x-y;
      v=v+u;
    }
  
    //post-condition
    /*@ assert x*u + y*v == a*b; */
  }   