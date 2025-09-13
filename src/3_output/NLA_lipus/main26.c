
/*@
    requires x == 1 && x <= y;
    */
    
int main26(int x, int y) {
	
	int z = 1;
	int w = 1;

	
            
        /*@
            loop invariant x >= 1 && x <= y; // x is within bounds
            loop invariant z == \product_from_1_to(x - 1, 1); // z accumulates the product of all x values up to x - 1
            loop invariant w == \product_from_1_to(x, 1); // w accumulates the product of all x values up to x
            loop assigns x, w, z;
            loop variant y - x;
        */
            while(x <= y)
	{
		w = w * x;
		if (x < y) {
			z = z * x;
		}
		x += 1;
	}
            

	/*@ assert w == z * y; */
	return 0;
}
