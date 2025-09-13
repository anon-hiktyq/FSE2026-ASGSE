/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \prod{integer k; 1 <= k < x} k;
	loop invariant z == \prod{int k | 1 <= k < x} k;
	loop invariant z == \product(j, 1, x - 1, j);
	loop invariant z == \product(i, 1, x - 1, i);
	loop invariant z == \product(1, x - 1);
	loop invariant z == \prod_{i=1}^{x-1} i;
	loop invariant z <= w;
	loop invariant x == 1 + z / w;
	loop invariant x <= y + 1;
	loop invariant x - 1 <= y;
	loop invariant w == z * y;
	loop invariant w == z * x;
	loop invariant w == z * x / x + 1;
	loop invariant w == z * (x - 1);
	loop invariant w == \prod{integer k; 1 <= k <= x - 1} k;
	loop invariant w == \prod{int k | 1 <= k <= x - 1} k;
	loop invariant w == \product(1, x - 1) * x;
	loop invariant w == \prod_{i=1}^{x-1} i * x;
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
	return; 
}
