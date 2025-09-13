/*@
  requires n > 0;
*/
void hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    /*@
    loop invariant 0 <= guess <= n;
    loop invariant 0 <= prev_guess <= n;
    loop invariant guess * guess <= 2 * n;
    loop invariant prev_guess != guess ==> prev_guess != (prev_guess + n / prev_guess) / 2;
    loop assigns prev_guess;
    loop assigns guess;
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}