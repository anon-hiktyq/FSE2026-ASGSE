/*@
  requires n > 0;
*/
void hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant prev_guess <= n;
    loop invariant prev_guess < n;
    loop invariant prev_guess * prev_guess <= n;
    loop invariant guess <= n;
    loop invariant guess * guess <= n + guess;
    loop invariant guess != prev_guess ==> guess * guess <= n;
    loop invariant \abs(guess - prev_guess) <= n;
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