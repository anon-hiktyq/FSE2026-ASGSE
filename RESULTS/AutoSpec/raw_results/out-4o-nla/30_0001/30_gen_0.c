
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (\old(z) + (\old(x) * \old(x)) * (\old(n) - n));
	loop invariant w == (\old(w) + (\old(y) * \old(y)) * (\old(n) - n));
	loop invariant p == (\old(p) + (\old(x) * \old(y)) * (\old(n) - n));
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
