/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \prod{int k | 1 <= k < x && x <= y + 1}(k);
	loop invariant z == \product(1, x - 1);
	loop invariant z == \prod_{k=1}^{x-1} k;
	loop invariant z == \prod(1, x - 1, x);
	loop invariant z == \prod(1, x - 1);
	loop invariant x > y ==> w == z * y;
	loop invariant x == 1 + \at(x, Pre);
	loop invariant x <= y + 1;
	loop invariant w == z * (x > y ? 1 : y);
	loop invariant w == z * (x <= y ? y : 1);
	loop invariant w == z * (x - 1);
	loop invariant w == \prod{int k | 1 <= k <= x - 1 && x <= y + 1}(k);
	loop invariant w == \product(1, x - 1) * (x <= y ? x : 1);
	loop invariant w == \prod_{k=1}^{x-1} k;
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
