/*@
requires a == 0 || a != 0;
requires a != 0;
ensures a == 0 ==> \result == 0;
ensures a != 0 ==> \result == 1;
ensures \result == 1;
ensures \result == 1 ==> a != 0;
ensures \result == 0 ==> a == 0;
assigns \nothing;
*/
int func(int a) {
    int x, y;
    int sum, res;
    if (a == 0){
        x = 0; y = 0;
    }
    else {
        x = 5; y = 5;
    }
    sum = x + y; 
    res = 10/sum; 
    return res;
}

int main() {
    int a = func(4);
    //@ assert a == 1;
    return 0;
}