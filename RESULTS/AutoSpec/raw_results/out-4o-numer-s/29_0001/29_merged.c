/*@
  requires n > 0;
*/
void hoo29(int n) {
    
    int guess;      
    int prev_guess; 

    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess == 0 || prev_guess * prev_guess <= n;
    loop invariant prev_guess <= n;
    loop invariant prev_guess != guess ==> \abs(guess - prev_guess) > 0;
    loop invariant prev_guess != guess ==> (guess - prev_guess) >= -1;
    loop invariant guess == prev_guess || guess != prev_guess;
    loop invariant guess <= n;
    loop invariant guess != prev_guess ==> \abs(guess - prev_guess) > 0;
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
    loop invariant 0 <= \abs(guess - prev_guess);
    loop invariant (prev_guess * prev_guess <= n);
    loop invariant (guess + 1) * (guess + 1) > n || guess * guess <= n;
    loop invariant (guess * guess <= n);
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
}