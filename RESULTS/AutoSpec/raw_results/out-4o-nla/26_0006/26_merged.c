/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z * x <= w;
	loop invariant x == y + 1 || z * x == w;
	loop invariant x - 1 <= y;
	loop invariant w == z * x || w == z * (x - 1) * x;
	loop invariant w == z * (x - 1);
	loop invariant \forall integer k; 1 <= k < x ==> w % k == 0;
	loop invariant 1 <= z && 1 <= w;
	loop invariant z <= w;
	loop invariant x >= 1 && x <= y + 1;
	loop invariant x <= y + 1;
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
