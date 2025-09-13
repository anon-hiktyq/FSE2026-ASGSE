/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \prod{int k; 1 <= k < x; k};
	loop invariant w == z * (x-1);
	loop invariant w == \prod{int k; 1 <= k <= x-1; k};
	loop invariant 1 <= z;
	loop invariant 1 <= w;
	loop invariant x <= y+1;
	loop invariant 1 <= x;
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
