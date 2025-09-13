
int unknown();

void foo05(int flag) {

	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

   
	/*@
	loop invariant x == y;;
	loop invariant x == y;
	loop invariant j == y * (y + 1) / 2;
	loop invariant j == y * (y + 1) / 2 || j == y * (y + 1) / 2 + y;
	loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);
	loop invariant j == i + y * flag;
	loop invariant j == (y * (y + 1)) / 2 + (flag ? y : 0);
	loop invariant j <= i + x;
	loop invariant i == x * (x + 1) / 2;
	loop invariant i == (x * (x + 1)) / 2;
	loop invariant i <= j;
	loop invariant i + flag * x <= j;
	loop invariant 0 <= y;
	loop invariant 0 <= x;
	loop invariant 0 <= j;
	loop invariant 0 <= i;
	loop assigns y;
	loop assigns x;
	loop assigns j;
	loop assigns i;
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