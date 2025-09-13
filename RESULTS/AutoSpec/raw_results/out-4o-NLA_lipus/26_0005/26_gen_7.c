/*@
requires x == 1 && x <= y;
*/
void main26(int x,int y){
	
	int z=1;
	int w=1;

	/*@
	loop invariant x <= y + 1;
	loop invariant z == w / x;
	loop invariant w == z * x;
	loop invariant w == \prod{integer i; 1 <= i < x}(i);
	loop invariant z == \prod{integer i; 1 <= i < x}(i);
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
