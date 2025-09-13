
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (n == 0 ? z : (\old(z) + x * x * (n - \old(n))));
	loop invariant w == (n == 0 ? w : (\old(w) + y * y * (n - \old(n))));
	loop invariant p == (n == 0 ? p : (\old(p) + x * y * (n - \old(n))));
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
