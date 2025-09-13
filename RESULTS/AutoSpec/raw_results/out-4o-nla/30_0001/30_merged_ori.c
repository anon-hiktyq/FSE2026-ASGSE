
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == \sum(0, \old(n)-n, x * x);
	loop invariant z == \old(z) + (x * x) * (\old(n) - n);
	loop invariant z == \old(z) + (x * x * (\old(n) - n));
	loop invariant z == (x * x) * (initial_n - n);
	loop invariant z == (n <= 0 ? 0 : z);
	loop invariant z == (\sum integer k; 0 <= k < n0 - n; x * x);
	loop invariant z == (\old(z) + (\old(x) * \old(x)) * (\old(n) - n));
	loop invariant z == (\at(z, Pre) + (n - \at(n, Pre)) * x * x);
	loop invariant w == \sum(0, \old(n)-n, y * y);
	loop invariant w == \old(w) + (y * y) * (\old(n) - n);
	loop invariant w == \old(w) + (y * y * (\old(n) - n));
	loop invariant w == (y * y) * (initial_n - n);
	loop invariant w == (n <= 0 ? 0 : w);
	loop invariant w == (\sum integer k; 0 <= k < n0 - n; y * y);
	loop invariant w == (\old(w) + (\old(y) * \old(y)) * (\old(n) - n));
	loop invariant w == (\at(w, Pre) + (n - \at(n, Pre)) * y * y);
	loop invariant p == \sum(0, \old(n)-n, x * y);
	loop invariant p == \old(p) + (x * y) * (\old(n) - n);
	loop invariant p == \old(p) + (x * y * (\old(n) - n));
	loop invariant p == (x * y) * (initial_n - n);
	loop invariant p == (n <= 0 ? 0 : p);
	loop invariant p == (\sum integer k; 0 <= k < n0 - n; x * y);
	loop invariant p == (\old(p) + (\old(x) * \old(y)) * (\old(n) - n));
	loop invariant p == (\at(p, Pre) + (n - \at(n, Pre)) * x * y);
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
