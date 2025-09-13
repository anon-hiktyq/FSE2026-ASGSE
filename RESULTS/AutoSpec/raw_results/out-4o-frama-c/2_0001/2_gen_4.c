
/*@
requires x >= INT_MIN && x <= INT_MAX;
requires y >= INT_MIN && y <= INT_MAX;
ensures \result == x + y;
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void moo2() {
    int a = add(1, 43);
    // @ assert a == 44;
    int b = add(997, 997);
}