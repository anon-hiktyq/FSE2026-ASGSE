/*@
requires x >= 0;
*/
int main(int x) {
	
	int z = w * x;

	while(unknown())
	{
		w = w * x;
		z = z * x;
	}

	/*@ assert z == w * x; */
	return 0;
}