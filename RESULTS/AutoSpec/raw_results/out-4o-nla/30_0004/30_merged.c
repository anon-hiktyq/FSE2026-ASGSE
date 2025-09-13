
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == (z - x * x * (n));
	loop invariant z == (z - x * x * (n + 1));
	loop invariant z == (z + (n - n) * x * x);
	loop invariant z == (n + 1) * x * x;
	loop invariant w == (w - y * y * (n));
	loop invariant w == (w - y * y * (n + 1));
	loop invariant w == (w + (n - n) * y * y);
	loop invariant w == (n + 1) * y * y;
	loop invariant p == (p - x * y * (n));
	loop invariant p == (p - x * y * (n + 1));
	loop invariant p == (p + (n - n) * x * y);
	loop invariant p == (n + 1) * x * y;
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
