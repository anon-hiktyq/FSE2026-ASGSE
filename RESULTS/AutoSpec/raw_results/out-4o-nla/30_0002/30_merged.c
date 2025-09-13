
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == (z - x * x * (n - 1));
	loop invariant z == (z - x * x * (n + 1)) + x * x * (n + 1);
	loop invariant z == (x * x) * (p / (x * y)) + (n * 0);
	loop invariant z == (n + 1) * x * x;
	loop invariant w == (y * y) * (p / (x * y)) + (n * 0);
	loop invariant w == (w - y * y * (n - 1));
	loop invariant w == (w - y * y * (n + 1)) + y * y * (n + 1);
	loop invariant w == (n + 1) * y * y;
	loop invariant p == x * y * (p / (x * y)) + (n * 0);
	loop invariant p == (p - x * y * (n - 1));
	loop invariant p == (p - x * y * (n + 1)) + x * y * (n + 1);
	loop invariant p == (n + 1) * x * y;
	loop invariant p * p <= z * w;
	loop invariant 0 <= z;
	loop invariant 0 <= w;
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
