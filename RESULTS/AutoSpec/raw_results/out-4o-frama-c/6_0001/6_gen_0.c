
/*@
requires x >= INT_MIN && x <= INT_MAX;
requires y >= INT_MIN && y <= INT_MAX;
ensures \result == x + y + 5;
assigns \nothing;
*/
int function(int x, int y) {
    int res ;
    y += 10 ;
    x -= 5 ;
    res = x + y ;
    // @ assert res == \at(x,Pre) + \at(y,Pre) + 5;
    return res ;
}

void moo6() {
    int t = function(-5, 5);
    // @ assert t == 5;
}