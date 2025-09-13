/*@
requires x >= 0;
requires y >= 0;
requires n >= 0;
*/
void main29(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (x * x) * (original_n - n);
	loop invariant w == (y * y) * (original_n - n);
	loop invariant p == (x * y) * (original_n - n);
	loop invariant z * w >= p * p;
	loop assigns z, w, p, n;
	*/
	while(n > 0) {
		z = z + x * x;
		w = w + y * y;
		p = p + x * y;
		n -= 1;
	}
    // post-condition
	// @ assert z * w >= p * p;
}
