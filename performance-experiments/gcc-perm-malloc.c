#include <stdlib.h>
#include <stdio.h>

int n = 11;
int *arr;
int *vis;
	    
void generate(int i) {
  if (i == n) {
    return;
  }

  for (int j = 0; j < n; ++j) {
    if (vis[j] == 0) {
      vis[j] = 1;
      arr[i] = j;
      generate(i+1);
      arr[i] = -1;
      vis[j] = 0;
    }
  }
}
  
int main() {
  arr = (int*)malloc(n * sizeof(int));
  vis = (int*)malloc(n * sizeof(int));

//  printf("%08X\n", arr);
//  printf("%08X\n", vis);

  for (int j = 0; j < n; ++j) {
    arr[j] = -1;
    vis[j] = 0;
  }

  generate(0);
  return 0;
}
