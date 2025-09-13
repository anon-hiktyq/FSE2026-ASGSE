int unknown();


void foo02() {
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;


	/*@
	loop invariant x == y;
	loop invariant w == 2 * y;
	loop invariant z % 2 == 1;
	loop assigns z;
	loop assigns x;
	loop assigns y;
	loop assigns w;
	*/
	while(unknown()) 
	{
		z += x + y + w;
		y++;
		if (z % 2 == 1) 
		  x++;
		w += 2; 
	}

	// @ assert x ==y ;
}
