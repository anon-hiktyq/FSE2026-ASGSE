
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo35(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((n@pre / 2 != 0) => (guess > 0) ) &&
((n@pre / 2 != 0) => (((prev_guess == 0)&&(guess == n@pre / 2)&&(n == n@pre)) || (prev_guess > 0 && guess > 0))) &&
((!(n@pre / 2 != 0)) => ((prev_guess == 0)&&(guess == n@pre / 2)&&(n == n@pre))) &&
(n == n@pre) &&
((guess == prev_guess) => (guess * guess <= n)
          loop assigns guess, prev_guess)
    */
    
            while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    
}