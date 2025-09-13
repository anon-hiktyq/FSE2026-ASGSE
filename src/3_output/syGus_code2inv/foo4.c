
void foo4(int y,int z) {
    int x = 0;   

    
    

            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant  ((x == 0)&&(z == \at(z,Pre))&&(y == \at(y,Pre))) || (y <= z);
            loop invariant  0 <= x <= 500;
            loop invariant z == \at(z,Pre);
            loop assigns x, y;
            */
            while(x < 500) {
   x += 1;
   if( z <= y) {
      y = z;
   }
}
            


   
    /*@ assert z >= y; */
}
