
/*@
    requires x >= 0 && y >= x;
    */
    
int main28(int x,int y) {
    // variable declarations
	
	int z=0;
	int w=0;
	int p=0;
    
    // loop body
	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(y,Pre)) ==> (z == w * x);
          loop invariant (0 < \at(y,Pre)) ==> (w >= 0 && w <= \at(y,Pre));
          loop invariant (0 < \at(y,Pre)) ==> (p == x * (1 + w) * w / 2);
          loop invariant (!(0 < \at(y,Pre))) ==> ((p == 0)&&(w == 0)&&(z == 0)&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop invariant x == \at(x,Pre);
          loop assigns z, w, p;
            */
            while(w < y) {
		z += x;
		p += z;
		w += 1;
	}
            
    // post-condition
	/*@ assert p == x * (1 + y) * y / 2; */

	return 0;
}
