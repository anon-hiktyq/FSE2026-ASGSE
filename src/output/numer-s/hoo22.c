
int hoo22(int a) { 
    
    //pre-condition
    int sn = 0;
    int x = 0;
  
    //loop-body
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant sn == x * a;
              loop invariant 0 <= x <= 10;
              loop invariant a == \at(a,Pre);
              loop assigns sn, x;
            */
            while(unknown()) {
      if (x<10) {
          sn = sn + a;
          x++;
      }
    }
            
  
    //post-condition
    /*@ assert sn == x*a || sn == 0; */
}
