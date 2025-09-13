/*@
  requires n > 0;
*/
void hoo35(int n) {
       
    int guess;      
    int prev_guess; 
    guess = n / 2;  
    prev_guess = 0; 

    /*@
    Looking at this square root computation using Newton's method, I need to identify the loop invariants that hold throughout the iterations.
    
    ```c
    loop invariant guess > 0;
    loop invariant prev_guess >= 0;
    loop invariant guess * guess >= n ==> guess * (guess - 1) < n;
    loop invariant guess != prev_guess ==> guess * guess >= n || (guess + 1) * (guess + 1) <= n;
    loop assigns guess;
    loop assigns prev_guess;
    ```
    */
    while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
    
    /*@ assert guess * guess <= n; */
}