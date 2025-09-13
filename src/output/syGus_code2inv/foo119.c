
void foo119(int size) {
 
    int i = 1;
    int sn = 0;
    
     
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (1 <= \at(size,Pre)) ==> (i == sn + 1);
          loop invariant (1 <= \at(size,Pre)) ==> (sn <= size);
          loop invariant !(1 <= \at(size,Pre) ) ==> ((sn == 0)&&(i == 1)&&(size == \at(size,Pre)));
          loop invariant size == \at(size,Pre);
          loop assigns i, sn;
            */
            while (i <= size) {
  
      i  = (i + 1);
      sn  = (sn + 1);
      
    }
            
  
    /*@ assert (sn != 0) ==> (sn == size);*/
  
  }
