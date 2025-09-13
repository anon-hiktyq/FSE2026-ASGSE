
/*@
  predicate valid_inputs(int x, int y, int n) = (x >= 0) && (y >= 0) && (n >= 0);
*/

/*@
    requires valid_inputs(x, y, n);
*/
int main29(int x,int y,int n) {
    // variable declarations
    int z=0;
    int w=0;
    int p=0;

    // loop body
	
            
        /*@ loop invariant 0 <= n <= \at(n,Pre);
            loop invariant z == (\at(n,Pre) - n) * (x * x);
            loop invariant w == (\at(n,Pre) - n) * (y * y);
            loop invariant p == (\at(n,Pre) - n) * (x * y);
            loop assigns z, w, p, n;
        */
        
            while(n > 0) {
		z = z + x * x;
		w = w + y * y;
		p = p + x * y;
		n -= 1;
	}
            
    // post-condition
    /*@ assert z * w >= p * p; */
}
