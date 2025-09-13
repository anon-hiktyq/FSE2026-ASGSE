/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x >= 1;
	loop invariant x <= y + 1;
	loop invariant w == z * (x == y + 1 ? 1 : x);
	loop invariant z == \prod{int k; 1 <= k < x && k < y}(k);
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
