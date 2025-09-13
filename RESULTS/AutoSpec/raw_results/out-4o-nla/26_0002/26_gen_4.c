/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant x >= 1;
	loop invariant x <= y + 1;
	loop invariant z == \prod{int k | 1 <= k < x && x <= y + 1}(k);
	loop invariant w == \prod{int k | 1 <= k <= x - 1 && x <= y + 1}(k);
	loop invariant w == z * (x > y ? 1 : y);
	loop assigns x, z, w;
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
