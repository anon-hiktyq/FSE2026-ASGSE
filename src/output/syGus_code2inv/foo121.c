
void foo121() {
 
    int i = 1;
    int sn = 0;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant i == 1 + sn;
      loop invariant sn >= 0;
      loop invariant sn <= 8;
      loop assigns i, sn;
    */
    while (i <= 8) {
  
      i  = (i + 1);
      sn  = (sn + 1);
      
    }
            
    /*@ assert (sn != 0) ==> (sn == 8);*/
}
