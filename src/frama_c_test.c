/*@requires \valid(a) && \valid(b);
   assigns *a, *b;
   ensures *a == \old(*b);
   ensures *b == \old(*a);
*/
void swap(int *a, int *b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(void) {
  int a = 42;
  int b = 37;

  swap(&a, &b);

  //@ assert a == 37 && b == 42;

  return 0;
}


void loop1(void) {
    int x = 0;
    /*@
       loop invariant 0 >= x >= -10;
       loop assigns x;
       loop variant x + 10;
     */
    while (x > -10) {
        --x;
    }
}

void loop2(void) {
    int x = -20;
    /*@
       loop invariant 4 > x >= -20;
       loop assigns x;
       loop variant -x;
     */
    while (x < 0) {
        x += 4;
    }
}


void foo(void) {
    int i;
    int x = 0;
    /*@
        loop invariant 0 <= i < 20;
        loop invariant 0 <= x <= 1;
        loop invariant \at(x, LoopCurrent) == 0;
        loop assigns x, i;
        loop variant 19 - i;
     */
    for (i = 0; i < 20; ++i) {
        if (i == 19) {
            x++;
            break;
        }
    }
    //@ assert x == 1;
    //@ assert i == 19;
}
