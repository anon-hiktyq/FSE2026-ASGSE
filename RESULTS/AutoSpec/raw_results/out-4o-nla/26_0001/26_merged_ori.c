/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \product(1, x - 1);
	loop invariant z == \prod_{k=1}^{x-1} k;
	loop invariant z == \prod(1, x - 1); // Represents the product of all integers from 1 to x-1.;
	loop invariant z == \prod(1, x - 1);
	loop invariant z == 1 || z == \prod(1, x - 1);
	loop invariant x >= 2 ==> w == \product(1, x - 1);
	loop invariant x >= 1 && x <= y + 1;
	loop invariant x <= y + 1;
	loop invariant x - 1 >= 1 && x - 1 <= y;
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
