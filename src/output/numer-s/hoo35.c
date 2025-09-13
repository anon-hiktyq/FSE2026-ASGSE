
/*@
    requires n > 0;
    */
    
int hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (!(\at(n,Pre) / 2 != 0)) ==> ((prev_guess == 0)&&(guess == \at(n,Pre) / 2)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
          loop assigns prev_guess, guess;
            */
            while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
            
    
    /*@ assert guess * guess <= n; */
}
