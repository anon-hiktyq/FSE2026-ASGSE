
/*@
requires \valid(a) && \valid(b);
ensures *a == \old(*b);
ensures *b == \old(*a);
assigns *a, *b;
*/
 void swap(int* a, int* b){
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

int main(){
    int a = 42;
    int b = 37;

    swap(&a, &b);

   

    return 0;
}