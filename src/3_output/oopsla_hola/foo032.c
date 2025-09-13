

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          PLACE_HOLDER_FOR_LOOP
            */
            for( n = 0 ; n < 2*k ; n++ ) {
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
            
  /*@ assert i ==j;*/
}
