
/*@
    requires x == 1 || x == 2;
    */
    
int hoo13(int x){

    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant  ((x == \at(x,Pre))) || (x == 1 || x == 2);
          loop assigns x;
            */
            while (unknown()) {
        if(x == 1) 
            x = 2;
        else if(x == 2)
            x = 1;
    }
            

    //post-condition
    /*@ assert x <= 8; */
}
