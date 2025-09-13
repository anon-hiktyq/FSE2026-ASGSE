
/*@
    requires a >= 1;
    requires b >= 1;
    */
    
int hoo28(int a,int b) { 
    int x,y,u,v;
  
    //pre-condition
    x=a;
    y=b;
    u=b;
    v=0;
    
  
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(a,Pre) > \at(b,Pre)) ==> (x*u + y*v == a*b);
          loop invariant (\at(a,Pre) > \at(b,Pre)) ==> (x >= 0);
          loop invariant (!(\at(a,Pre) > \at(b,Pre))) ==> ((v == 0) && (u == \at(b,Pre)) && (y == \at(b,Pre)) && (x == \at(a,Pre)) && (b == \at(b,Pre)) && (a == \at(a,Pre)));
          loop invariant u == \at(b,Pre);
          loop invariant y == \at(b,Pre);
          loop invariant b == \at(b,Pre);
          loop invariant a == \at(a,Pre);
          loop assigns x, v;
            */
            while(x > y) {
      x = x - y;
      v = v + u;
    }
            
  
    //post-condition
    /*@ assert x*u + y*v == a*b; */
}
