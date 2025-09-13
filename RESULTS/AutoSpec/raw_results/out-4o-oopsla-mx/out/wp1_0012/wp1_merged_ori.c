/*@
requires 0 <= y <= 10;;
requires 0 <= y <= 10;
requires -INT_MAX <= y <= INT_MAX;
requires -INT_MAX <= x <= INT_MAX;
requires -2147483648 <= y <= 2147483647;
requires -2147483648 <= x <= 2147483647;
requires -10 <= y <= 0;
requires -10 <= x <= 10 && -10 <= y <= 10;
requires -10 <= x <= 0;;
requires -10 <= x <= 0;
ensures \result == x - 5 + y + 10;
ensures \result == x - 5 + (y + 10);
ensures \result == (x - 5) + (y + 10);
ensures -15 <= \result <= 5;;
ensures -15 <= \result <= 5;
assigns \nothing;;
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