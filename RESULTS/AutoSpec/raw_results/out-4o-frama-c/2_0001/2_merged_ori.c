
/*@
requires y >= INT_MIN && y <= INT_MAX;
requires x >= INT_MIN && x <= INT_MAX;
requires x + y >= INT_MIN && x + y <= INT_MAX;
requires x + y <= INT_MAX && x + y >= INT_MIN;
requires \true;
requires INT_MIN - y <= x <= INT_MAX - y;
ensures \result >= INT_MIN && \result <= INT_MAX;
ensures \result == x + y;
assigns \nothing;
```c;
```;
*/
int add(int x, int y) {
    return x+y;
}

void moo2() {
    int a = add(1, 43);
    // @ assert a == 44;
    int b = add(997, 997);
}