
void foo05(int flag) {

	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

   
	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant x >= 0;
          loop invariant y >= 0;
          loop invariant j == (y * (y + 1)) / 2 + (flag ? y : 0);
          loop invariant i == (x * (x + 1)) / 2;
          loop invariant j >= i + (y * (flag ? 1 : 0));
          loop invariant flag == \at(flag,Pre);
          loop assigns x, y, j, i;
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
             
	/*@ assert j>=i; */
	
}
