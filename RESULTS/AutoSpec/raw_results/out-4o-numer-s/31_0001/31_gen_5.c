/*@
  requires A >= 1;
  requires (R-1)*(R-1) < A;
  requires A <= R*R;
  requires A%2 ==1;
*/
void hoo31(int A, int R) { 
    int u,v,r;
  
    //pre-condition
    u=2*R+1;
    v=1;
    r=R*R-A; 
  
    //loop-body
    /*@
    loop invariant 0 <= v;
    loop invariant 2*R + 1 == u;
    loop invariant r + A == R*R - (v - 1)/2;
    loop invariant r >= 0;
    loop assigns r;
    loop assigns v;
    */
    while(r>0) {
      r=r-v;
      v=v+2;
    }
  
    //post-condition
    /*@ assert 4*(A+r) == u*u-v*v-2*u+2*v; */
  }   