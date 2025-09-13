
int goo2(int x, int y) {
    int r = x;
    int d = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (r + d * y == \at(x,Pre));
          loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> (d >= 0);
          loop invariant (!(\at(x,Pre) >= \at(y,Pre))) ==> ((d == 0)&&(r == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop invariant x == \at(x,Pre);
          loop assigns r, d;
            */
            while (r >= y) {
       
        // Beginning
        r = r - y;
        d = d + 1;
        // ENd
        //@ assert r + d*y == x;
    }
            
    return d;
}
