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
	loop invariant z == i - j + x * (x - 1) / 2 + y * (y - 1) / 2 + w * (w - 1) / 2;
	loop invariant 0 <= y <= x;
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
