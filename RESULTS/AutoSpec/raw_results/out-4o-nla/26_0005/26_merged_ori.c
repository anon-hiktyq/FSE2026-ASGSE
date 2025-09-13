/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \prod(integer i; 1 <= i < x && x <= y + 1; i);
	loop invariant z == \prod(1, x - 1);
	loop invariant z <= w;
	loop invariant x >= 1 && x <= y + 1;
	loop invariant x <= y + 1;
	loop invariant w == z * x;
	loop invariant w == z * (x - 1);
	loop invariant 1 <= z;
	loop invariant 1 <= x;
	loop invariant 1 <= w;
	loop assigns z;
	loop assigns x;
	loop assigns w;
	*/
	while(x <= y)
	{
		w = w * x;
		if (x < y) {
			z = z * x;
		}
		x += 1;
	}

	// @ assert w == z * y;
	return 0;
}
