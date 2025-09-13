
/*@
    requires x >= 0 && x <= 10;
    */
    
int hoo32(int x) {
	
	int y = x * x;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(x,Pre) * \at(x,Pre) <= 1000) ==> (y == \at(x,Pre) * \at(x,Pre) + (x - \at(x,Pre))) ;
          loop invariant (\at(x,Pre) * \at(x,Pre) <= 1000) ==> (x >= \at(x,Pre)) ;
          loop invariant (\at(x,Pre) * \at(x,Pre) <= 1000) ==> (y <= x * x) ;
          loop invariant (\at(x,Pre) * \at(x,Pre) <= 1000) ==> (y <= 1000 + 2*x + 1) ;
          loop invariant (\at(x,Pre) * \at(x,Pre) <= 1000) ==> (x * x > 1000 ==> y <= 1000) ;
          loop invariant (!(\at(x,Pre) * \at(x,Pre) <= 1000)) ==> ((y == \at(x,Pre) * \at(x,Pre))&&(x == \at(x,Pre)));
          loop assigns x, y;
            */
            while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}
            

	/*@ assert y <= 1000; */
	return 0;
}
