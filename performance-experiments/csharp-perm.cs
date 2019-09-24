using System.Numerics;
using System;
using System.IO;
using System.Diagnostics;

class Permutation {
    class Bctk {
        int n;
        int[] arr;
        bool[] vis;

        public Bctk(int nn) {
            n = nn;
            arr = new int[n];
            vis = new bool[n];

            int j = 0;
            while (j < n) {
                arr[j] = -1;
                vis[j] = false;
                j = j + 1;
            }
        }

        public void generate(int i) {
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
    }

    static void Main() {
        Bctk p = new Bctk(11);
        p.generate(0);
    }
}
