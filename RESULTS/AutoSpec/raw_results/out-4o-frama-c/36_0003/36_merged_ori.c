/*@
requires \valid(a) && \valid(b) && \valid(c);
requires \separated(a, b, c);
ensures \old(*c) == *a || \old(*c) == *b || \old(*c) == *c;
ensures \old(*c) <= \old(*b) <= \old(*a) ==> *a == \old(*c) && *b == \old(*b) && *c == \old(*a);
ensures \old(*c) <= \old(*a) <= \old(*b) ==> *a == \old(*c) && *b == \old(*a) && *c == \old(*b);
ensures \old(*b) == *a || \old(*b) == *b || \old(*b) == *c;
ensures \old(*b) <= \old(*c) <= \old(*a) ==> *a == \old(*b) && *b == \old(*c) && *c == \old(*a);
ensures \old(*b) <= \old(*a) <= \old(*c) ==> *a == \old(*b) && *b == \old(*a) && *c == \old(*c);
ensures \old(*a) == *a || \old(*a) == *b || \old(*a) == *c;
ensures \old(*a) <= \old(*c) <= \old(*b) ==> *a == \old(*a) && *b == \old(*c) && *c == \old(*b);
ensures \old(*a) <= \old(*b) <= \old(*c) ==> *a == \old(*a) && *b == \old(*b) && *c == \old(*c);
ensures \exists integer x, y, z; {x, y, z} == {*a, *b, *c} && \old({*a, *b, *c}) == {x, y, z};
ensures \exists int x, y, z; {*a, *b, *c} == {x, y, z} && {x, y, z} == \old(*a, *b, *c);
ensures *a <= *b <= *c;
ensures *a <= *b && *b <= *c;
assigns *a, *b, *c;
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