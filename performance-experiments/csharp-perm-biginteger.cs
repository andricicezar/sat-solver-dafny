using System.Numerics;
using System;
using System.IO;
using System.Diagnostics;

class Permutation {
    class Bctk {
        BigInteger n;
        BigInteger[] arr;
        bool[] vis;

        public Bctk(BigInteger nn) {
            n = nn;
            arr = new BigInteger[(int)n];
            vis = new bool[(int)n];

            BigInteger j = new BigInteger(0);
            while (j < n) {
                arr[(int)j] = new BigInteger(-1);
                vis[(int)j] = false;
                j = j + new BigInteger(1);
            }
        }

        public void generate(BigInteger i) {
            if (i == n) {
                return;
            }

            BigInteger j = new BigInteger (0);
            while (j < n) {
                if (!vis[(int)j]) {
                    vis[(int)j] = true;
                    arr[(int)i] = j;
                    generate(i+ (new BigInteger(1)));
                    arr[(int)i] = new BigInteger(-1);
                    vis[(int)j] = false;
                }
                j = j + new BigInteger(1);
            }
        }
    }

    static void Main() {
        Bctk p = new Bctk(11);
        p.generate(0);
    }
}
