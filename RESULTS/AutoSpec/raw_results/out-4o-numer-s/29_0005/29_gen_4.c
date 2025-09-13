/*@
  requires n > 0;
*/
void hoo29(int n) {
    
    int guess;      
    int prev_guess; 

    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant guess >= 0;
    loop invariant prev_guess >= 0;
    loop invariant guess != prev_guess ==> (guess - prev_guess != 0);
    loop invariant (prev_guess + 1) * (prev_guess + 1) > n || (guess + 1) * (guess + 1) <= n;
    loop invariant (guess + 1) * (guess + 1) > n;
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert (guess + 1) * (guess + 1) > n; */
}