
/*@
    requires n >= 0;
    */
    
int main20(int n){
    // variable declarations
    int a, s, t;

    //precondition
    a = 0;
    s = 1;
    t = 1;

    // loop body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant a >= 0;
            loop invariant t == 1 + 2 * a;
            */
            while(s <= n){
     a = a + 1;
     t = t + 2;
     s = s + t;
    }
            

    // post-condition
    /*@ assert( n < (a + 1) * (a + 1)); */
}
