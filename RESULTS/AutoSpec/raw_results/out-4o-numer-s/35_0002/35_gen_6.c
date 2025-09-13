/*@
  requires n > 0;
*/
void hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess != guess ==> 0 < guess <= n;
    loop invariant prev_guess >= 0;
    loop invariant guess * guess - n <= 0;
    loop invariant prev_guess * prev_guess <= n;
    loop assigns prev_guess, guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}