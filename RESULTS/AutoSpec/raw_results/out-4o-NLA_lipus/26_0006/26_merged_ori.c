/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == w / x;
	loop invariant z == \product(1, x - 1, \lambda integer k; k);
	loop invariant z == \product(1, x - 1);
	loop invariant z == 1;
	loop invariant z == 1 || x > y;
	loop invariant z <= w;
	loop invariant z * y == w || (x > y && w == z * (x-1));
	loop invariant x > 1 ==> \forall integer k; 1 <= k < x ==> z == k!;
	loop invariant x <= y + 1;
	loop invariant x - 1 <= y;
	loop invariant w == z * x;
	loop invariant w == \product(1, x - 1, \lambda integer k; k);
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
