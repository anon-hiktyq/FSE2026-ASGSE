
/*@
    requires x >= 0;
    */
    
int main22(int x) {
	
	int y = x * x;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant y <= x * x;
          loop invariant x >= \at(x, Pre); // x is at least the initial value
          loop invariant y == \at(x, Pre) * \at(x, Pre) + (x - \at(x, Pre));
          loop assigns x, y;
            */
            while(unknown()) {
		x = x + 1;
		y = y + 1;
	}
            

	/*@ assert y <= x * x; */
	return 0;
}
