
/*@
    requires i >= 0 && j >= 0;
    */
    
void foo009(int i, int j) {

    int x = i;
    int y = j;
    

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(i,Pre) != 0) ==> (x >= 0);
          loop invariant (\at(i,Pre) != 0) ==> (y == \at(j,Pre) - (\at(i,Pre) - x));
          loop invariant (!(\at(i,Pre) != 0)) ==> ((y == \at(j,Pre))&&(x == \at(i,Pre))&&(j == \at(j,Pre))&&(i == \at(i,Pre)));
          loop invariant j == \at(j,Pre);
          loop invariant i == \at(i,Pre);
          loop assigns x, y;
            */
            while (x != 0) {
        x--;
        y--;
    }
            

    if (i == j) {
        /*@ assert y == 0;*/
    }
}
