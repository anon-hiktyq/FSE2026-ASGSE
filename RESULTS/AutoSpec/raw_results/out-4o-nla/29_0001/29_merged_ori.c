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
	loop invariant z == (x * x) * (p / (x * y));
	loop invariant z == (x * x) * (original_n - n);
	loop invariant z == (x * x) * (initial_n - n);
	loop invariant w == (y * y) * (p / (x * y));
	loop invariant w == (y * y) * (original_n - n);
	loop invariant w == (y * y) * (initial_n - n);
	loop invariant p == x * y * (z / (x * x));
	loop invariant p == (x * y) * (original_n - n);
	loop invariant p == (x * y) * (initial_n - n);
	loop invariant p * p <= z * w;
	loop invariant n;
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
