/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess * prev_guess <= n;
    loop invariant prev_guess != guess ==> (prev_guess > 0 && guess > prev_guess / 2);
    loop invariant guess * guess <= n || prev_guess * prev_guess <= n;
    loop invariant guess * guess <= n || (prev_guess * prev_guess <= n);
    loop invariant guess * guess <= n || (guess - 1) * (guess - 1) > n;
    loop invariant guess * guess <= n + 2 * guess;
    loop invariant guess * guess <= n + 2 * guess - 1;
    loop invariant guess != prev_guess ==> guess > prev_guess || prev_guess > guess;
    loop invariant guess != prev_guess ==> (guess > prev_guess || prev_guess > guess);
    loop invariant guess != prev_guess ==> (guess - prev_guess <= n / guess);
    loop invariant guess != prev_guess ==> (guess * guess > n || prev_guess * prev_guess > n);
    loop invariant guess != prev_guess ==> (guess * guess > n && prev_guess * prev_guess > n) || (guess * guess <= n && prev_guess * prev_guess <= n);
    loop invariant guess != prev_guess ==> ((guess - prev_guess) * (guess - prev_guess)) >= 1;
    loop invariant \abs(guess * guess - n) <= \abs(prev_guess * prev_guess - n);
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= \abs(guess - prev_guess);
    loop invariant 0 < guess;
    loop invariant (\exists integer g; g * g <= n < (g + 1) * (g + 1)) ==> (guess == g || prev_guess == g);
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}