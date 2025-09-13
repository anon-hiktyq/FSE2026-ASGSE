
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == (z - x * x * n);
	loop invariant z == (x * x) * (initial_n - n);
	loop invariant z == (p / y) * x;
	loop invariant z == (n == 0 ? \old(z) + (x * x * (\old(n) - n)) : z);
	loop invariant z == (\old(z) + (n * x * x));
	loop invariant w == y * y * (p / y);
	loop invariant w == (y * y) * (initial_n - n);
	loop invariant w == (w - y * y * n);
	loop invariant w == (n == 0 ? \old(w) + (y * y * (\old(n) - n)) : w);
	loop invariant w == (\old(w) + (n * y * y));
	loop invariant p == (x * y) * (initial_n - n);
	loop invariant p == (p - x * y * n);
	loop invariant p == (n == 0 ? \old(p) + (x * y * (\old(n) - n)) : p);
	loop invariant p == (\old(p) + (n * x * y));
	loop invariant p * p <= z * w;
	loop invariant 0 <= n;
	loop assigns z;
	loop assigns w;
	loop assigns p;
	loop assigns n;
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
