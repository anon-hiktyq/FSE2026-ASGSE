/*@
requires -100 <= x <= 100;
requires -100 <= y <= 100;
assigns \nothing;
ensures \result == x + y + 5;
ensures -15 <= \result <= 5;
*/
int function(int x, int y) {
    int res ;
    y += 10 ;
    x -= 5 ;
    res = x + y ;
    // @ assert -15 <= res <= 5;
    return res ;
}

// write a test
void main() {
    int t = function(-5, 5);
    // @ assert t == 0;
}