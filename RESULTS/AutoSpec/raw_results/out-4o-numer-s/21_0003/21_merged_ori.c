/*@
  requires X > 0;
  requires Y > 0;
  requires X >= Y;
*/
void hoo21(int X,int Y) {
    
    int v, x, y;

    v = 2 * Y - X;
    y = 0;
    x = 0;


    
    /*@
    loop invariant y <= x;
    loop invariant x <= X+1;
    loop invariant x <= X + 1;
    loop invariant v == 2*Y*x - 2*x*y - X + 2*Y;
    loop invariant v == 2*Y - X + 2*y*(Y - X) + 2*x*Y;
    loop invariant v == 2*Y - X + 2*Y*x - 2*x*y - 2*y;
    loop invariant v == 2 * Y * x - 2 * x * y - X + 2 * Y;
    loop invariant v == 2 * Y * x - 2 * x * y - X + 2 * Y + 2 * y;
    loop invariant v == 2 * Y * x - 2 * X * y + 2 * Y - X;
    loop invariant v <= 2*Y;
    loop invariant 2*Y*x - 2*x*y - X + 2*Y - v + 2*y == 0;
    loop invariant 2 * y <= x;
    loop invariant 2 * Y * x - 2 * x * y - X + 2 * Y - v + 2 * y == 0;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant -X <= v;
    loop assigns y;
    loop assigns x;
    loop assigns v;
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