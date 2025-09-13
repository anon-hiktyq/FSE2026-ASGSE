
/*@
requires \valid(a) && \valid(b);
ensures \result == \max(*a, *b);
assigns \nothing;
*/
int max_ptr(int *a, int *b){
    return (*a < *b) ? *b : *a ;
}

extern int h;

int main() {
    h = 42;
    int a = 24;
    int b = 42;

    int x = max_ptr(&a, &b);

  
}