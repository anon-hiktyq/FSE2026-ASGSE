


int hoo21(int X,int Y) 
{
    
    int v, x, y;

    v = 2 * Y - X;
    y = 0;
    x = 0;


    
    
            
            /*@
          loop invariant (0 <= \at(X,Pre)) ==> ((x == 0) ==> ((y == 0)&&(v == 2 * \at(Y,Pre) - \at(X,Pre))&&(Y == \at(Y,Pre))&&(X == \at(X,Pre))));
          loop invariant (0 <= \at(X,Pre)) ==> (0 <= x <= X + 1) ;
          loop invariant (0 <= \at(X,Pre)) ==> (0 <= y <= x) ;
          loop invariant (!(0 <= \at(X,Pre))) ==> ((y == 0)&&(x == 0)&&(v == 2 * \at(Y,Pre) - \at(X,Pre))&&(Y == \at(Y,Pre))&&(X == \at(X,Pre)));
          loop invariant Y == \at(Y,Pre);
          loop invariant X == \at(X,Pre);
            */
            while (x <= X) {
        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        x++;

    }
            

    
    /*@ assert 2*Y*x - 2*x*y - X + 2*Y - v + 2*y == 0; */
}