/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess <= n;
    loop invariant prev_guess <= guess;
    loop invariant guess <= n;
    loop invariant guess * guess <= n || guess * guess > n;
    loop invariant \abs(guess - prev_guess) <= \abs(n/2);
    loop invariant \abs(guess - prev_guess) <= \abs(n);
    loop invariant \abs(guess - n/guess) <= \abs(prev_guess - n/prev_guess);
    loop invariant \abs(guess * guess - n) < \abs(prev_guess * prev_guess - n) || prev_guess == guess;
    loop invariant 1 <= guess;
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
    loop invariant 0 <= \abs(guess - prev_guess);
    loop invariant 0 < guess;
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}