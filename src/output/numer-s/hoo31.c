
/*@
    requires A >= 1;
    requires (R-1)*(R-1) < A;
    requires A <= R*R;
    requires A%2 ==1;
    */
    
int hoo31(int A, int R) { 
    int u,v,r;
  
    //pre-condition
    u=2*R+1;
    v=1;
    r=R*R-A; 
  
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant v % 2 == 1; // v is always odd
            loop invariant 4 * (A + r) + v * v + 2 * u - 2 * v == u * u;
            loop assigns r, v;
            */
            while(r > 0) {
      r = r - v;
      v = v + 2;
    }
            
  
    //post-condition
    /*@ assert 4*(A+r) == u*u-v*v-2*u+2*v; */
}
