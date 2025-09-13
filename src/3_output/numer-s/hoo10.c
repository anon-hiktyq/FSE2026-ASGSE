
int hoo10(){

    //pre-condition
    int x = 1;
    int y = 0;
    
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant  ((y == 0)&&(x == 1)) || (x == 0);
          loop invariant  y >= 0 && y <= 1024;
          loop assigns x, y;
            */
            while (y < 1024) {
        x = 0;
        y = y + 1;
    }
            

    //post-condition
    /*@ assert x == 0; */
}
