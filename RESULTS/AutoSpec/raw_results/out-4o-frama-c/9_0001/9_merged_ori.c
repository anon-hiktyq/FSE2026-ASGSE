/*@
requires y >= INT_MIN && y <= INT_MAX;
requires x >= INT_MIN && x <= INT_MAX;
requires \valid(&x) && \valid(&y);
requires \true;;
requires \true;
requires INT_MIN <= y <= INT_MAX;
requires INT_MIN <= x <= INT_MAX;
requires INT_MIN <= x <= INT_MAX && INT_MIN <= y <= INT_MAX;
ensures \result == x - y;;
ensures \result == x - y;
assigns \nothing;;
assigns \nothing;
*/
int diff (int x, int y) {
    return x-y;
}

void moo9() {
    int t = diff(10, 5);
    // @ assert t == 5;
}