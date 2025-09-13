/*@
  requires n > 0;
*/
void hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant 0 < guess <= n;
    loop invariant 0 <= prev_guess < n;
    loop invariant guess != prev_guess;
    loop invariant prev_guess >= guess / 2;
    loop assigns guess;
    loop assigns prev_guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}