/*@
requires -15 <= x + y && x <= x - 5 && y <= y + 10;  
ensures -15 <= \result && \result <= 5;  
assigns x, y;
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