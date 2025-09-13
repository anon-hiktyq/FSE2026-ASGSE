/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess == (guess + n / guess) / 2 || guess == n / 2;
    loop invariant prev_guess <= guess;
    loop invariant prev_guess <= (guess + prev_guess) / 2;
    loop invariant prev_guess < n;
    loop invariant prev_guess * prev_guess <= n;
    loop invariant prev_guess != guess;
    loop invariant n <= guess * guess;
    loop invariant guess <= n;
    loop invariant guess * guess <= n || (guess - prev_guess) == 0;
    loop invariant guess * guess <= n || (guess - prev_guess) < 0;
    loop invariant guess * guess <= n + prev_guess * prev_guess;
    loop invariant guess != prev_guess;
    loop invariant guess != prev_guess ==> prev_guess == (guess + n / guess) / 2;
    loop invariant \abs(guess - prev_guess) <= n / 2;
    loop invariant \abs(guess - prev_guess) < \abs(2 * guess);
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
    loop invariant 0 < guess;
    loop invariant (guess - prev_guess) * (guess - prev_guess) <= n;
    loop invariant (guess * guess <= n);
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}