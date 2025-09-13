/*@
  requires n > 0;
*/
void hoo24(int n,int guess,int prev_guess) {


    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess == 0 || guess != prev_guess;
    loop invariant guess > 0;
    loop invariant prev_guess >= 0;
    loop invariant guess * guess <= n;
    loop assigns guess;
    loop assigns prev_guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}