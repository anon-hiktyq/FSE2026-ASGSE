
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (p / y) * x + (x * x) * (n - (\at(n, Pre) - 1));
	loop invariant w == (p / x) * y + (y * y) * (n - (\at(n, Pre) - 1));
	loop invariant p == (\at(n, Pre) - n) * x * y;
	loop invariant z * w >= p * p;
	loop invariant \at(n, Pre) >= n;
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
