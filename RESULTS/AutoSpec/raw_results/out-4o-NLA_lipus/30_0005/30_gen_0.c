
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (x*x)*(n - (\at(n, Pre)));
	loop invariant w == (y*y)*(n - (\at(n, Pre)));
	loop invariant p == (x*y)*(n - (\at(n, Pre)));
	loop assigns n;
	loop assigns z;
	loop assigns w;
	loop assigns p;
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
