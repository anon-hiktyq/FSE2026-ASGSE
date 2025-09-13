/*@
  requires a >= 1;
  requires b >= 1;
*/
void hoo33(int a, int b) { 
    int x,y,u,v;
  
    //pre-condition
    x=a;
    y=b;
    u=b;
    v=0;
    
  
    //loop-body
    /*@
    loop invariant y == b;
    loop invariant x*u + y*v == a*b;
    loop invariant x * u + y * v == a * b;
    loop invariant v == u * ((a - x) / y);
    loop invariant v == (b * ((a - x) / y));
    loop invariant v == (a - x) * u / y;
    loop invariant u == b;
    loop invariant \exists integer k; x == a - k * b && v == k * b;
    loop invariant 1 <= y;
    loop invariant 1 <= x;
    loop invariant 1 <= x + y*v;
    loop invariant 0 <= x;
    loop invariant 0 <= v;
    loop invariant 0 < y;
    loop invariant 0 < x;
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