
void foo128(int y) {

    int x = 1;
    
    /*@
      loop invariant x >= 1;
      loop variant y - x;
    */
    while (x < y) {
  
       x  = x + x ;
       
    }
            
    /*@ assert x >= 1;*/
  
}
