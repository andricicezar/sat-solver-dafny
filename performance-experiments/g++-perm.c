#include <vector>

using namespace std;

class Bctk {
public:
  int n;
  vector<int> arr;
  vector<bool> vis;
	    
  Bctk(int nn) : arr(nn), vis(nn) {
    n = nn;

    int j = 0;
    while (j < n) {
      arr[j] = -1;
      vis[j] = false;
      j = j + 1;
    }
  }

  void generate(int i) {
    if (i == n) {
      return;
    }
    
    int j = 0;
    while (j < n) {
      if (!vis[j]) {
        vis[j] = true;
        arr[i] = j;
        generate(i+1);
        arr[i] = -1;
        vis[j] = false;
      }
      j = j + 1;
    }
  }
};
  
int main()
{
  Bctk p(11);
  p.generate(0);
  return 0;
}
