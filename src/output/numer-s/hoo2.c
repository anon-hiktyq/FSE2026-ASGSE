
int hoo2(){
    //pre-condition
    int x = 5;
   
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant x % 8 == 5;
            loop invariant x >= 5;
            loop assigns x;
            */
            while(unknown()){
        x = x + 8;
    }
            

    //post-condition
    /*@ assert (x % 8) == 5; */
}
