
/*@
requires \valid(b);
requires \valid(a);
requires \valid(a) && \valid(b);
ensures *b ==> *a == 0;
ensures *b == true ==> *a == 0;
ensures *b == false ==> *a == \old(*a);
ensures *b == 1 ==> *a == 0;
ensures *b == 0 ==> *a == \old(*a);
ensures *b != 0 ==> *a == 0;
ensures (*b == 1) ==> *a == 0;
ensures (*b == 0) ==> *a == \old(*a);
ensures !(*b) ==> *a == \old(*a);
assigns *a;
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){
    if(*b) *a = 0 ;
}

int main(){
    int a = 5 ;
    int x = 0 ;
    reset_1st_if_2nd_is_true(&a, &x);
  

    int const b = 1 ;
    reset_1st_if_2nd_is_true(&a, &b);
 
}

