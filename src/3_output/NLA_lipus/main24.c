
/*@
    requires x >= 0 && y >= 0;
    */
    
int main24(int x,int y) {
	
	int z = x * y;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(x,Pre) > 0) ==> (x >= 0);
          loop invariant (\at(x,Pre) > 0) ==> (z == \at(x,Pre) * \at(y,Pre) - (\at(x,Pre) - x) * \at(y,Pre));
          loop invariant (!(\at(x,Pre) > 0)) ==> ((z == \at(x,Pre) * \at(y,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop assigns x, z;
            */
            while(x > 0) {
		x = x - 1;
		z = z - y;
	}
            

	/*@ assert z == 0; */
	return 0;
}
