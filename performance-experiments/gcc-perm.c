#include <stdlib.h>

int n = 11;
int arr[11];
int vis[11];
	    
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
  for (int j = 0; j < n; ++j) {
    arr[j] = -1;
    vis[j] = 0;
  }

  generate(0);
  return 0;
}
