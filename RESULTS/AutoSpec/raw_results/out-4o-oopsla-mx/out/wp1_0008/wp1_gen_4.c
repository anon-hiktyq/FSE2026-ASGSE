/*@
requires -20 <= x <= 20;
requires -20 <= y <= 20;
ensures \result == x + y + 5;
ensures -15 <= \result <= 45;
assigns \nothing;
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