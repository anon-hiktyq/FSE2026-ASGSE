/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant w == z * x;
	loop invariant x - 1 <= y;
	loop invariant 1 <= z && 1 <= w;
	loop invariant \forall integer k; 1 <= k < x ==> w >= z;
	loop invariant x <= y + 1;
	loop invariant z <= w;
	loop assigns z;
	loop assigns w;
	loop assigns x;
	loop invariant z <= w;
	loop invariant x <= y + 1;
	loop invariant x <= y + 1 && w >= z;
	loop invariant x - 1 <= y;
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
