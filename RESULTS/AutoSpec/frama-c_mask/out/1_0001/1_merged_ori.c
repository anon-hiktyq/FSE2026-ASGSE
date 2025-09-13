
/*@
requires height >= 0;
requires base >= 0;;
requires base >= 0;
ensures \result == (base * height) / 2;;
ensures \result == (base * height) / 2;
assigns \nothing;
*/
int area(int base, int height){
    int res = (base *  height)/2;
    return res;
}

int main() {
    int a = area(4, 5);
    return 0;
}
