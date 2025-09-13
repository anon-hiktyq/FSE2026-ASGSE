/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess == guess || prev_guess != guess;
    loop invariant prev_guess < n;
    loop invariant prev_guess * prev_guess <= n;
    loop invariant prev_guess * prev_guess <= n + prev_guess;
    loop invariant prev_guess != guess ==> guess != prev_guess;
    loop invariant guess <= n;
    loop invariant guess <= n / 2 + 1;
    loop invariant guess * guess <= n || guess * guess > n;
    loop invariant guess * guess <= n || (prev_guess * prev_guess <= n && guess > prev_guess);
    loop invariant 0 <= prev_guess;
    loop invariant 0 <= guess;
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