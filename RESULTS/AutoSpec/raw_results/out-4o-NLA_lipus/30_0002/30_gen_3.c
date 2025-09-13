
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (p / x) * x + (x * x) * (initial_n - n);
	loop invariant w == (p / y) * y + (y * y) * (initial_n - n);
	loop invariant p == (initial_n - n) * x * y;
	loop invariant z * w >= p * p;
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
