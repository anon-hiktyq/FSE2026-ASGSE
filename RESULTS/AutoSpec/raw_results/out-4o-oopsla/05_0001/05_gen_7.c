
int unknown();

void foo05(int flag) {

	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

   
	/*@
	loop invariant x == y;
	loop invariant i <= j;
	loop invariant x >= 0;
	loop invariant y >= 0;
	loop invariant i == (x * (x + 1)) / 2;
	loop invariant j == (y * (y + 1)) / 2 + (flag ? y : 0);
	loop assigns x;
	loop assigns y;
	loop assigns i;
	loop assigns j;
	*/
	while(unknown())
	{
	  x++;
	  y++;
	  i += x;
	  j += y;
	  if (flag){
	  	j+=1;
      }
	} 
	// @ assert j>=i;
	
}