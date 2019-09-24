newtype {:nativeType "int"} int32 = x | -0x80000000 <= x < 0x80000000

class Btck {
  var n : int32;
  var arr : array<int32>;
  var vis : array<bool>;

  constructor(n' : int32)
    requires n' >= 0;
  {
    n := n';
    
    new;

    arr := new int32[n];
    vis := new bool[n];

    var j := 0;
    while (j < n) {
      arr[j] := -1;
      vis[j] := false;
      j := j + 1;
    }
  }

  method generate(i : int32) {
    if (i == n) {
      return;
    }

    var j := 0;
    while (j < n) {
      if (!vis[j]) {
        vis[j] := true;
        arr[i] := j;
        generate(i+1);
        arr[i] := -1;
        vis[j] := false;
      }
      j := j + 1;
    }
  }
}

method Main() { 
  var p := new Btck(11);
  p.generate(0);
} 
