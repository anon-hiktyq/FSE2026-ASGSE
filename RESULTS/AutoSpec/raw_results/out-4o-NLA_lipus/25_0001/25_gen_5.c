int unknown();
/*@
requires x >= 0;
*/
void main25(int x, int w){
	
	int z = w * x;

	/*@
	loop invariant z == w * x;
	loop invariant x >= 0;
	loop assigns w;
	loop assigns z;
	*/
	while(unknown())
	{
		w = w * x;
		z = z * x;
	}

	// @ assert z == w * x;
	return; 
}