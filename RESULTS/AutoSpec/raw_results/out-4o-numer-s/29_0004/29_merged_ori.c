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
    loop invariant prev_guess <= n / 2;
    loop invariant prev_guess <= guess;
    loop invariant prev_guess < n;
    loop invariant prev_guess != guess;
    loop invariant n < (guess + 1) * (guess + 1);
    loop invariant guess <= n;
    loop invariant guess <= n / 2 + 1;
    loop invariant guess != prev_guess;
    loop invariant guess != prev_guess ==> (2*guess + n/guess - prev_guess) / 2 > prev_guess;
    loop invariant \forall integer m; m > 0 && m * m <= n ==> guess >= m;
    loop invariant \forall integer k; 0 <= k <= prev_guess ==> k*k <= n;
    loop invariant \forall integer g; g != prev_guess ==> (g + 1) * (g + 1) > n;
    loop invariant \exists integer q; q * q <= n && (q + 1) * (q + 1) > n;
    loop invariant \abs(guess - prev_guess) < n;
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
    loop invariant 0 <= (prev_guess - guess) * (prev_guess - guess);
    loop invariant 0 < guess;
    loop invariant 0 < \abs(guess - prev_guess);
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert (guess + 1) * (guess + 1) > n; */
}