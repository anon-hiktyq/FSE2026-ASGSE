/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \prod{int k; 1 <= k < x && k < y}(k);
	loop invariant z == \product(1, x - 1, \lambda integer k; k);
	loop invariant z == \prod(1, x - 1);
	loop invariant x > y || w == z * y;
	loop invariant x <= y + 1;
	loop invariant x - 1 <= y;
	loop invariant w == z * (x == y + 1 ? 1 : x);
	loop invariant w == z * (x - 1);
	loop invariant w == \product(1, x - 1, \lambda integer k; k);
	loop invariant w == \product(1, x - 1, \lambda integer k; k) * (x <= y ? x : 1);
	loop invariant \forall integer k; 1 <= k < x ==> w % k == 0;
	loop invariant 2 <= x;
	loop invariant 1 <= z;
	loop invariant 1 <= x;
	loop invariant 1 <= w;
	loop invariant 0 < z;
	loop invariant 0 < w;
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
