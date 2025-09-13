/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant 1 <= x <= y+1;
	loop invariant w == x == y+1 ? y * z : \product{int k; 1 <= k < x; k};
	loop invariant z == \product{int k; 1 <= k < x; k};
	loop assigns x, w, z;
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
