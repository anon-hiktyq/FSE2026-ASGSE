/*@
requires 0 <= y <= 10;
requires -5 <= y <= 5;
requires -5 <= y <= 15;
requires -20 <= x <= 10;
requires -1000 <= y <= 1000;
requires -1000 <= x <= 1000;
requires -100 <= y <= 100;
requires -100 <= x <= 100;
requires -10 <= x <= 10;
ensures \result == x - 5 + (y + 10);
ensures \result == x + y + 5;
ensures \result == (x - 5) + (y + 10);
assigns \nothing;
*/
int function(int x, int y) {
    int res ;
    y += 10 ;
    x -= 5 ;
    res = x + y ;
    //@ assert -15 <= res <= 5;
    return res ;
}

// write a test
void main() {
    int t = function(-5, 5);
    //@ assert t == 0;
}