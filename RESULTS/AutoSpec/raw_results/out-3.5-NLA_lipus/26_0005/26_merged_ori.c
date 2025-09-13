/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant z == \product{int k; 1 <= k < x && k < y; k};
	loop invariant x > 1 ==> w == z * (x <= y ? 1 : y);
	loop invariant x <= y+1;
	loop invariant w == \product{int k; 1 <= k < x; k};
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
