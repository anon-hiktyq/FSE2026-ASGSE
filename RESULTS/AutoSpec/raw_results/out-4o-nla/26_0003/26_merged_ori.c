/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \product(k, 1, x - 1, k);
	loop invariant z == \product(1, x - 1, k); // Product of integers from 1 to (x - 1);
	loop invariant z == \product(1, x - 1, k -> k);
	loop invariant z == \prod {k | 1 <= k < x};
	loop invariant z * x == w;
	loop invariant x >= 1 && x <= y + 1;
	loop invariant x <= y + 1;
	loop invariant x - 1 <= y;
	loop invariant w == z * (x - 1);
	loop invariant w == \product(1, x - 1, k) * z;;
	loop invariant w == \prod {k | 1 <= k <= (x - 1)};
	loop invariant 1 <= z;
	loop invariant 1 <= x;
	loop invariant 1 <= x - 1;
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
