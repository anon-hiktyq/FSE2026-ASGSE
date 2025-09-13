/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x - 1 <= y;
	loop invariant z == \product(1, x - 1, \lambda integer k; k);
	loop invariant w == \product(1, x - 1, \lambda integer k; k) * (x <= y ? x : 1);
	loop invariant x >= 1;
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
	return; 
}
