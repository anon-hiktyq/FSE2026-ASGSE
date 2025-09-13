
void foo6(int v1, int v2 ,int v3,int size, int y, int z) {
    
    int x = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 < \at(size, Pre) ==> (0 <= x <= \at(size, Pre)));
            loop invariant (0 < \at(size, Pre) ==> (x == 0 ==> (y == \at(y, Pre) && z == \at(z, Pre))));
            loop invariant (0 < \at(size, Pre) ==> (x > 0 ==> (y <= z)));
            loop assigns y, x;
            */
            while(x < size) {
       x += 1;
       if( z <= y) {
          y = z;
       }
    }
            

    /*@ assert (size > 0) ==> (z >= y);  */

}
