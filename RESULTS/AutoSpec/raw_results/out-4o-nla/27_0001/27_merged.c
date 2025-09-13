/*@
requires x >= 0 && y >= x;
*/
int main27(int x,int y) {
	
	int z=0;
	int w=0;

	/*@
	loop invariant z == x * w;
	loop invariant z == w * x;
	loop invariant x >= 0 && y >= x;
	loop invariant x <= y;
	loop invariant w <= y;
	loop invariant 0 <= x;
	loop invariant 0 <= w;
	loop assigns z;
	loop assigns w;
	*/
	while(w < y) {
		z += x;
		w += 1;
	}

	//@ assert z == x * y;

	return 0;
}
