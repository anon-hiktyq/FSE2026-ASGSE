/*@
requires x == 1 && x <= y;
*/
int main26(int x,int y) {
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \product(1, x - 1);;
	loop invariant z == \product(1, x - 1);
	loop invariant z <= w;;
	loop invariant z * x <= w;
	loop invariant x >= 1 && z + (y - x + 1) == w / (x == y + 1 ? 1 : x);
	loop invariant x >= 1 && x <= y + 1;;
	loop invariant x == y + 1 || z * x == w;
	loop invariant x <= y + 1;;
	loop invariant x - 1 <= y;;
	loop invariant x - 1 <= y;
	loop invariant w; <= z * y;
	loop invariant w == z * x;;
	loop invariant w == z * x || w == z * (x - 1) * x;
	loop invariant w == z * (x - 1);
	loop invariant w == \product(1, x - 1) * x;;
	loop invariant \forall integer k; 1 <= k < x ==> z == \prod(1, k);
	loop invariant \forall integer k; 1 <= k < x ==> w % k == 0;;
	loop invariant \forall integer k; 1 <= k < x ==> w % k == 0;
	loop invariant \forall integer k; 1 <= k < x - 1 ==> z % k == 0;;
	loop invariant 1 <= z;;
	loop invariant 1 <= z && 1 <= w;
	loop invariant 1 <= x;;
	loop invariant 1 <= w;;
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
