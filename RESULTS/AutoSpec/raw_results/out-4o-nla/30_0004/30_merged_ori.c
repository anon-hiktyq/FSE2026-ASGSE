
int main30(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == \sum(0, x * x, n);
	loop invariant z == (z - x * x * (n));
	loop invariant z == (z - x * x * (n + 1));
	loop invariant z == (z + (n - n) * x * x);
	loop invariant z == (n + 1) * x * x;
	loop invariant z == (\at(z, Pre) + (x * x) * (\at(n, Pre) - n));
	loop invariant z == (\at(z, Pre) + (x * x * (\at(n, Pre) - n)));
	loop invariant z == (\at(z, Pre) + (\at(n, Pre) - n) * x * x);
	loop invariant w == \sum(0, y * y, n);
	loop invariant w == (w - y * y * (n));
	loop invariant w == (w - y * y * (n + 1));
	loop invariant w == (w + (n - n) * y * y);
	loop invariant w == (n + 1) * y * y;
	loop invariant w == (\at(w, Pre) + (y * y) * (\at(n, Pre) - n));
	loop invariant w == (\at(w, Pre) + (y * y * (\at(n, Pre) - n)));
	loop invariant w == (\at(w, Pre) + (\at(n, Pre) - n) * y * y);
	loop invariant p == \sum(0, x * y, n);
	loop invariant p == (p - x * y * (n));
	loop invariant p == (p - x * y * (n + 1));
	loop invariant p == (p + (n - n) * x * y);
	loop invariant p == (n + 1) * x * y;
	loop invariant p == (\at(p, Pre) + (x * y) * (\at(n, Pre) - n));
	loop invariant p == (\at(p, Pre) + (x * y * (\at(n, Pre) - n)));
	loop invariant p == (\at(p, Pre) + (\at(n, Pre) - n) * x * y);
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
