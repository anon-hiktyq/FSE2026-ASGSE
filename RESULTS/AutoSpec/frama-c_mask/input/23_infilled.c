
/* @ >>> INFILL <<< */
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

