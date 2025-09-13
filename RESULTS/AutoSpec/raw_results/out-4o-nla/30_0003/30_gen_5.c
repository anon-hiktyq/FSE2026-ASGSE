
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (n == 0 ? \old(z) + (x * x * (\old(n) - n)) : z);
	loop invariant w == (n == 0 ? \old(w) + (y * y * (\old(n) - n)) : w);
	loop invariant p == (n == 0 ? \old(p) + (x * y * (\old(n) - n)) : p);
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
