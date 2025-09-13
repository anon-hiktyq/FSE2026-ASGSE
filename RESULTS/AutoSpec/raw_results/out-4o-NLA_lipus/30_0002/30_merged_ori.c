
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == p*x + n*x*x;
	loop invariant z == \at(z, Pre) + (x * x) * (\at(n, Pre) - n);
	loop invariant z == (p / y) * x;
	loop invariant z == (p / x) * x + (x * x) * (initial_n - n);
	loop invariant z == (p / x) * x + (n * x * x);
	loop invariant x * y == 0 || p % (x * y) == 0;
	loop invariant w == p*y + n*y*y;
	loop invariant w == \at(w, Pre) + (y * y) * (\at(n, Pre) - n);
	loop invariant w == (p / y) * y + (y * y) * (initial_n - n);
	loop invariant w == (p / y) * y + (n * y * y);
	loop invariant w == (p / x) * y;
	loop invariant p == \at(p, Pre) + (x * y) * (\at(n, Pre) - n);
	loop invariant p == (x*y)*(n+1)/2;
	loop invariant p == (n * x * y);
	loop invariant p == (initial_n - n) * x * y;
	loop invariant p * p <= z * w;
	loop invariant n == 0 ==> z * w >= p * p;
	loop invariant \exists integer k; k >= 0 && n == \old(n) - k;
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
