/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant x <= y + 1;
	loop invariant x >= 2;
	loop invariant w == z * x;
	loop invariant z == w / x;
	loop assigns x;
	loop assigns w;
	loop assigns z;
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
