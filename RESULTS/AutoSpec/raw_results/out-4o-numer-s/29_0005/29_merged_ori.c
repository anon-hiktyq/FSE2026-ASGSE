/*@
  requires n > 0;
*/
void hoo29(int n) {
    
    int guess;      
    int prev_guess; 

    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess <= n;
    loop invariant prev_guess <= guess;
    loop invariant prev_guess < n;
    loop invariant prev_guess * prev_guess <= n;
    loop invariant prev_guess != guess;
    loop invariant prev_guess != guess ==> (guess * guess) > n;
    loop invariant n < (guess + 1) * (guess + 1);
    loop invariant guess <= n;
    loop invariant guess * guess <= n;
    loop invariant guess != prev_guess;
    loop invariant guess != prev_guess ==> (guess - prev_guess) * (guess - prev_guess) > 0;
    loop invariant guess != prev_guess ==> (guess - prev_guess != 0);
    loop invariant \abs(guess - prev_guess) <= n;
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
    loop invariant 0 < n;
    loop invariant 0 < guess;
    loop invariant (prev_guess == 0) || (guess != prev_guess);
    loop invariant (prev_guess == 0 || (prev_guess * prev_guess) <= n);
    loop invariant (prev_guess + 1) * (prev_guess + 1) > n || (guess + 1) * (guess + 1) <= n;
    loop invariant (prev_guess * prev_guess <= n) && (guess * guess <= n);
    loop invariant (guess - prev_guess) * (guess - prev_guess) <= n;
    loop invariant (guess + 1) * (guess + 1) > n || guess * guess <= n;
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert (guess + 1) * (guess + 1) > n; */
}