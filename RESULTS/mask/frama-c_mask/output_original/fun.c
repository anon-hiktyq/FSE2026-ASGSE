

int fun(int x, int y) 
{
    int r = x;
    int d = 0;

    
            
            /*@
          loop invariant (\at(x,Pre) >= \at(y,Pre)) ==> ((r + d * \at(y,Pre) == \at(x,Pre)) && (d >= 0)) ;
          loop invariant (!(\at(x,Pre) >= \at(y,Pre))) ==> ((d == 0)&&(r == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop invariant x == \at(x,Pre);
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