
void foo04(int x,int y) {


  x = -50;
  
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          PLACE_HOLDER_FOR_LOOP
            */
            while( x < 0 ) {
	x = x + y;
	y++;
  }
            
  /*@ assert y > 0;*/
}

