
int hoo12(int y){

    //pre-condition
    int x = 0;
    
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant x >= 0; // x is non-negative
          loop assigns x;
            */
            while (x < 99) {
        if(y % 2 == 0){
            x = x + 2;
        } 
        else{
            x = x + 1;
        }
    }
            

    //post-condition
    /*@ assert (x % 2) == (y % 2); */
}
