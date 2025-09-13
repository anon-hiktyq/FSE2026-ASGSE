
void main30(int x,int y,int n){
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z >= 0;
	loop invariant w >= 0;
	loop invariant p * p <= z * w;
	loop assigns z, w, p, n;
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
