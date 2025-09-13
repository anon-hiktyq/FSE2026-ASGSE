/*@
requires x >= 0;
requires y >= 0;
requires n >= 0;
*/
int main29(int x,int y,int n) {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    // loop body
	/*@
	loop invariant n >= 0;
	loop invariant z == (\old(z) + (x * x) * (n - \old(n)));
	loop invariant w == (\old(w) + (y * y) * (n - \old(n)));
	loop invariant p == (\old(p) + (x * y) * (n - \old(n)));
	loop invariant z * w >= p * p;
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
