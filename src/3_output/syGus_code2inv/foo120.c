
void foo120() {
 
    int i = 1;
    int sn = 0;
    
     
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant i == sn + 1;
            loop invariant sn >= 0;
            loop invariant 1 <= i <= 9;
            loop assigns i, sn;
            */
            while (i <= 8) {
  
      i  = (i + 1);
      sn  = (sn + 1);
      
    }
            
  
    /*@ assert (sn != 8) ==> (sn == 0);*/
  
}
