
/*@
    requires 0 <= i && i < 1000000;
    requires j >= 0;
    */
    
void foo0010(int i, int j) {

    int x = i;
    int y = j;
    int z = 0;
  
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(i,Pre) != 0) ==> (0 <= x <= \at(i,Pre));
          loop invariant (\at(i,Pre) != 0) ==> (y == \at(j,Pre) - 2 * (\at(i,Pre) - x));
          loop invariant (\at(i,Pre) != 0) ==> (z == \at(i,Pre) - x);
          loop invariant (!(\at(i,Pre) != 0)) ==> ((z == 0)&&(y == \at(j,Pre))&&(x == \at(i,Pre))&&(j == \at(j,Pre))&&(i == \at(i,Pre)));
          loop invariant j == \at(j,Pre);
          loop invariant i == \at(i,Pre);
          loop assigns x, y, z;
            */
            while (x != 0) {
        x--;
        y -= 2;
        z++;
    }
            

    if (i == j) {
        /*@ assert y == -z; */
    }
    
}
