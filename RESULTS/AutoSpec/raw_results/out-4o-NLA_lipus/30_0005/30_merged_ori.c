
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == x*x*(n0 - n);
	loop invariant z == w || z > w;
	loop invariant z == (x*x)*(n - (\at(n, Pre)));
	loop invariant z == (p / y) * x + (x * x) * (n - (\at(n, Pre) - 1));
	loop invariant z == (\old(z) + (x*x)*(n-\old(n)));
	loop invariant z == (\at(z, Pre) + (x * x) * (\at(n, Pre) - n));
	loop invariant w == y*y*(n0 - n);
	loop invariant w == (y*y)*(n - (\at(n, Pre)));
	loop invariant w == (p / x) * y + (y * y) * (n - (\at(n, Pre) - 1));
	loop invariant w == (\old(w) + (y*y)*(n-\old(n)));
	loop invariant w == (\at(w, Pre) + (y * y) * (\at(n, Pre) - n));
	loop invariant p == x*y*(n0 - n);
	loop invariant p == (x*y)*(n - (\at(n, Pre)));
	loop invariant p == (\old(p) + (x*y)*(n-\old(n)));
	loop invariant p == (\at(p, Pre) + (x * y) * (\at(n, Pre) - n));
	loop invariant p == (\at(n, Pre) - n) * x * y;
	loop invariant p * p <= z * w;
	loop invariant n <= \at(n, Pre);
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
