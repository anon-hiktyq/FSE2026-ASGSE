/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == w / x;
	loop invariant z == \prod_{k=1}^{x-1} k;
	loop invariant z <= w;
	loop invariant z * y == w * x;
	loop invariant z * x == w;
	loop invariant x >= 1 && x <= y + 1;
	loop invariant x <= y + 1;
	loop invariant x - 1 <= y;
	loop invariant w == z * x;
	loop invariant w == z * (x - 1);
	loop invariant 2 <= x;
	loop invariant 1 <= x;
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
