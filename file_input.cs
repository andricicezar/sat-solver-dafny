using System;
using System.Collections;

namespace @FileInput {
    public partial class @Reader
    {
        public static char[] getContent() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
                return System.IO.File.ReadAllText(argList[1]).ToCharArray();
            }

            return "".ToCharArray();
        }

        public static long getTimestamp() {
          return DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
        }
    }
}
