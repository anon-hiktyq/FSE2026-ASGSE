/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant guess > 0;
    loop invariant prev_guess >= 0;
    loop invariant guess != prev_guess ==> (guess * guess > n || prev_guess * prev_guess > n);
    loop invariant (\exists integer g; g * g <= n < (g + 1) * (g + 1)) ==> (guess == g || prev_guess == g);
    loop assigns guess, prev_guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}