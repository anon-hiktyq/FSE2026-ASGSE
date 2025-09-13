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
	loop invariant z == \old(z) + (x * x) * (\old(n) - n);
	loop invariant z == (x * x) * (p / (x * y));
	loop invariant z == (\at(z,Pre) + (x * x) * (\at(n,Pre) - n));
	loop invariant z == (\at(z, Pre) + (x * x) * (initial_n - n));
	loop invariant w == \old(w) + (y * y) * (\old(n) - n);
	loop invariant w == (y * y) * (p / (x * y));
	loop invariant w == (\at(w,Pre) + (y * y) * (\at(n,Pre) - n));
	loop invariant w == (\at(w, Pre) + (y * y) * (initial_n - n));
	loop invariant p == \old(p) + (x * y) * (\old(n) - n);
	loop invariant p == (x * y) * (p / (x * y));
	loop invariant p == (\at(p,Pre) + (x * y) * (\at(n,Pre) - n));
	loop invariant p == (\at(p, Pre) + (x * y) * (initial_n - n));
	loop invariant p * p <= z * w;
	loop invariant 0 <= z;
	loop invariant 0 <= w;
	loop invariant 0 <= p;
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
