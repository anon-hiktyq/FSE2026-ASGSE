/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x - 1 <= y;
	loop invariant z == \product(j, 1, x - 1, j);
	loop invariant w == z * x;
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
