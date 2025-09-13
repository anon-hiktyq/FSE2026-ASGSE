int unknown();
/*@
requires x >= 0;
*/
void main25(int x, int w){
	
	int z = w * x;

	/*@
	*/
	while(unknown())
	{
		w = w * x;
		z = z * x;
	}

	// @ assert z == w * x;
	return; 
}