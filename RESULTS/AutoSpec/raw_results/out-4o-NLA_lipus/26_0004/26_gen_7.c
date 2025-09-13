/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x <= y + 1;
	loop invariant z == \prod_{i=1}^{x-1} i;
	loop invariant w == \prod_{i=1}^{x-1} i * x;
	loop invariant w == z * x;
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
