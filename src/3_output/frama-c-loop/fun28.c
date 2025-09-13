
int fun28(int x, int y , int *r) {
    *r = x;
    int d = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (*r + d * y == \at(x,Pre));
            loop invariant (\at(*r,Pre) >= \at(y,Pre)) ==> (d >= 0);
            loop invariant y == \at(y,Pre);
            loop invariant x == \at(x,Pre);
            loop assigns *r, d;
            */
            while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
            
    return d;
}
