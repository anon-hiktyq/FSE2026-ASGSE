
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (x * x) * (p/y);
	loop invariant w == (y * y) * (p/x);
	loop invariant z * w >= p * p;
	loop invariant x != 0 && y != 0 ==> p == (z / (x * x)) * y;
	loop assigns n, z, w, p;
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
