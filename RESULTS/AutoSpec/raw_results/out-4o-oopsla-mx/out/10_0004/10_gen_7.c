#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main() {


  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /*@
  loop invariant x == y;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop invariant x <= y + 1;
  loop invariant y <= x + 1;
  loop assigns x;
  loop assigns y;
  loop assigns w;
  loop assigns z;
  */
  while(unknown2()){
  	if(w) {
  	  x++;
  	  w = !w;
	  }
	
    if(!z) {
      y++; 
      z=!z;
    }
  }

  // @ assert x==y;
  
}
