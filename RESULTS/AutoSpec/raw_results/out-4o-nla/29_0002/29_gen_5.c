/*@
requires x >= 0;
requires y >= 0;
requires n >= 0;
*/
int main29(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (\at(z,Pre) + (x * x) * (\at(n,Pre) - n));
	loop invariant w == (\at(w,Pre) + (y * y) * (\at(n,Pre) - n));
	loop invariant p == (\at(p,Pre) + (x * y) * (\at(n,Pre) - n));
	loop invariant z * w >= p * p;
	loop assigns n, z, w, p;
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
