typedef struct s {
    int *a;
} s;

void fun(s *p) {
    *(p->a) = *(p->a)+1;
}
