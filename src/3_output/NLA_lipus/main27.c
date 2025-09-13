
/*@
  logic integer z; // Declare z as a logic variable
  predicate sum(int x, int w) = z == x * w;
*/

/*@
    requires x >= 0 && y >= x;
    */
    
int main27(int x,int y) {
	
	int z=0;
	int w=0;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(y,Pre)) ==> (z == x * w);
          loop invariant (0 < \at(y,Pre)) ==> (0 <= w <= \at(y,Pre));
          loop invariant (!(0 < \at(y,Pre))) ==> ((w == 0)&&(z == 0)&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop invariant x == \at(x,Pre);
          loop assigns z, w;
            */
            while(w < y) {
		z += x;
		w += 1;
	}
            

	/*@ assert z == x * y; */

	return 0;
}
