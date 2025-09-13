/*@
x <= y && y <= z &&;
requires \valid(a) && \valid(b) && \valid(c);
ensures \old(*c) == *a || \old(*c) == *b || \old(*c) == *c;
ensures \old(*b) == *a || \old(*b) == *b || \old(*b) == *c;
ensures \old(*a) == *a || \old(*a) == *b || \old(*a) == *c;
ensures \exists integer x, y, z;;
ensures \exists int x, y, z; x <= y && y <= z && {x, y, z} == {*a, *b, *c};
ensures *a <= *b && *b <= *c;
assigns *a, *b, *c;
*a == x && *b == y && *c == z;
(z == \old(*a) || z == \old(*b) || z == \old(*c)) &&;
(y == \old(*a) || y == \old(*b) || y == \old(*c)) &&;
(x == \old(*a) || x == \old(*b) || x == \old(*c)) &&;
*/
void order_3(int *a, int *b, int *c) {
    if (*a > *b) {
        int temp = *a;
        *a = *b;
        *b = temp;
    }
    if (*a > *c) {    
        int temp = *a;
        *a = *c;
        *c = temp;
    }
    if (*b > *c) {
        int temp = *b;
        *b = *c;
        *c = temp;
    }
}

void moo18(){
    
    int a1 = 5, b1 = 3, c1 = 4 ;
    order_3(&a1, &b1, &c1) ;
    // @ assert a1 == 3 && b1 == 4 && c1 == 5;
    
    int a2 = 2, b2 = 2, c2 = 2 ;
    order_3(&a2, &b2, &c2) ;
    // @ assert a2 == 2 && b2 == 2 && c2 == 2 ;

    int a3 = 4, b3 = 3, c3 = 4 ;
    order_3(&a3, &b3, &c3) ;
    // @ assert a3 == 3 && b3 == 4 && c3 == 4 ;

    int a4 = 4, b4 = 5, c4 = 4 ;
    order_3(&a4, &b4, &c4) ;
    // @ assert a4 == 4 && b4 == 4 && c4 == 5 ;
}