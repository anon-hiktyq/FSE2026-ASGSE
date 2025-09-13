
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == x*x*(initial_n - n);
	loop invariant z == w || z > w;;
	loop invariant z == p / (x * y) * x * x;
	loop invariant z == n * x * x;
	loop invariant z == (x * x) * (p / (x * y));
	loop invariant w == y*y*(initial_n - n);
	loop invariant w == p / (x * y) * y * y;
	loop invariant w == n * y * y;
	loop invariant w == (y * y) * (p / (x * y));
	loop invariant p == x*y*(initial_n - n);
	loop invariant p == n * x * y;
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
