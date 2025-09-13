
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant z == x*x*(w/x/y);
	loop invariant z == (x * x) * (p/y);
	loop invariant z == (p / x) * x;
	loop invariant z == (p * p) / (x * x);
	loop invariant x != 0 && y != 0 ==> p == (z / (x * x)) * y;
	loop invariant w == y*y*(z/x/x);
	loop invariant w == (y * y) * (p/x);
	loop invariant w == (p / y) * y;
	loop invariant w == (p * p) / (y * y);
	loop invariant p*p <= z*w;
	loop invariant p == x*y*(z/x/x);
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
