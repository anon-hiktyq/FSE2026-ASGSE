
int unknown();

void foo05(int flag) {

	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

   
	/*@
	loop invariant x == y;
	loop invariant i <= j;
	loop invariant 0 <= i;
	loop invariant 0 <= j;
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