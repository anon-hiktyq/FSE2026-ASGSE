/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant guess >= 0;
    loop invariant prev_guess >= 0;
    loop invariant prev_guess != guess;
    loop invariant guess * guess <= n + 2 * n / prev_guess;
    loop invariant 0 < guess <= n / 2 + 1;
    loop assigns prev_guess, guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}