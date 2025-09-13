/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x - 1 >= 1;
	loop invariant x <= y + 1;
	loop invariant w == z * (x - 1);
	loop invariant w == \product(1, x - 1);
	loop invariant z == \product(1, x - 1);
	loop assigns x;
	loop assigns w;
	loop assigns z;
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
