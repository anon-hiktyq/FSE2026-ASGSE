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
	loop invariant z - x - y - w == i - j;
	loop invariant w == 2 * y;
	loop invariant z % 2 == 1;
	loop assigns x;
	loop assigns y;
	loop assigns w;
	loop assigns z;
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
