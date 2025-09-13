/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x >= 1;
	loop invariant x <= y+1;
	loop invariant z == w / x;
	loop invariant z * y == w;
	loop invariant x == y+1 ==> w == z * y;
	loop assigns x;
	loop assigns z;
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
