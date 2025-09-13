
/*@
  predicate valid_state(int x, int y) = 
      x >= 0 && x <= 10 && 
      y == x * x;
*/

/*@
    requires x >= 0 && x <= 10;
*/
int main23(int x) {
	
	int y = x * x;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant x >= 0 && x <= 10;
            loop assigns x, y;
            */
            while(unknown()) {
		x = x + 1;
		y = y + 1;
	}
            

	/*@ assert y <= x * x; */
	return 0;
}
