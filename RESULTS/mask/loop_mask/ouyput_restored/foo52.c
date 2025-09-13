
void foo52()
{
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;

	/* >>> LOOP INVARIANT TO FILL <<< */
	/*@
	  loop invariant w == 2 * y;
	  loop invariant x >= 0;
	  loop invariant y >= 0;
	  loop invariant w >= 0;
	  loop invariant z >= i - j;
	  loop assigns z, x, y, w;
	  loop variant y; // Assuming y decreases with each iteration
	*/
	while(unknown()) 
	{
		z += x + y + w;
		y++;
		if (z % 2 == 1) 
		  x++;
		w += 2; 
	}

	/* mask_1 */
    /*@ assert x ==y ;*/
}
