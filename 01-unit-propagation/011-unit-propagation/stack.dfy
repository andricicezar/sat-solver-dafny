predicate InRange(lo : int, hi : int, i : int) {
  lo <= i < hi
}

predicate identity<T>(v : T) {
  v == v
}

function RangeSet(lo: int, hi: int): set<int>
{
    set i | lo <= i < hi && InRange(lo, hi, i)
}

lemma CardinalityRangeSet(lo: int, hi: int)
    decreases hi - lo
    ensures |RangeSet(lo, hi)| == if lo >= hi then 0 else hi - lo
{
    if lo < hi {
        assert RangeSet(lo, hi) == {lo} + RangeSet(lo + 1, hi);
        CardinalityRangeSet(lo + 1, hi);
    }
}

class Stack {
  var size : int;
  var stack : array<seq<(int, bool)>>;
  var variablesCount : int;
  ghost var contents : set<(int, bool)>;

  constructor(varCount : int) 
    requires varCount > 0;

    ensures valid();
    ensures this.variablesCount == varCount;
    ensures this.contents == {};
    ensures forall x :: 0 <= x < stack.Length ==> |stack[x]| == 0;
    ensures fresh(stack);
  {
    this.size := 0;
    this.variablesCount := varCount;
    this.stack := new seq<(int, bool)>[varCount];
    this.contents := {};

    new;

    var i := 0;
    while (i < stack.Length) 
      modifies stack;
      invariant 0 <= i <= stack.Length;
      invariant forall j :: 0 <= j < i ==> stack[j] == [];
      decreases stack.Length - i;
    {
      stack[i] := [];
      i := i + 1;
    }
  }

  predicate validVariablesCount() 
    reads this;
  {
    variablesCount > 0
  }

  predicate validVariable(variable : int)
    reads this;
    requires validVariablesCount();
  {
    0 <= variable < variablesCount
  }

  predicate valid()
    reads this, stack;
  {
    validVariablesCount() &&

    stack.Length == variablesCount &&

    (0 <= size <= stack.Length) &&

    (forall i :: 0 <= i < size-1 ==>
      |stack[i]| > 0) 

    &&

    (forall i :: size <= i < stack.Length ==>
      stack[i] == [])

    &&

    (forall i :: 0 <= i < stack.Length ==>
      forall j :: 0 <= j < |stack[i]| ==>
        validVariable(stack[i][j].0))

    &&

    (forall i :: 0 <= i < stack.Length ==>
      forall j :: 0 <= j < |stack[i]| ==> (
        (forall i' :: 0 <= i' < stack.Length && i != i' ==>
          forall j' :: 0 <= j' < |stack[i']| ==>
            stack[i][j].0 != stack[i'][j'].0) &&
        (forall j' :: 0 <= j' < |stack[i]| && j != j' ==>
            stack[i][j].0 != stack[i][j'].0)
      ))

    &&

    (forall i :: 0 <= i < stack.Length ==>
      forall j :: 0 <= j < |stack[i]| ==>
        stack[i][j] in contents)

    &&

    (forall c :: c in contents ==>
      exists i,j :: 0 <= i < stack.Length 
                 && 0 <= j < |stack[i]| 
                 && stack[i][j] == c)
  }

  function getLastLayer() : set<(int, bool)>
    reads this, stack;
    requires 0 < size <= stack.Length;
  {
    set x | x in stack[size-1] && identity(x)
  }

  lemma variableNotInContents_variableNotInStack(variable : int)
    requires valid();
    requires (variable, false) !in contents &&
          (variable, true) !in contents;

    ensures forall i,j :: 0 <= i < stack.Length 
          && 0 <= j < |stack[i]| ==>
            stack[i][j].0 != variable;
  {
    assert (forall c :: c in contents ==>
      exists i,j :: 0 <= i < stack.Length
                 && 0 <= j < |stack[i]|
                 && stack[i][j] == c);
    assert (forall i :: 0 <= i < stack.Length ==>
      forall j :: 0 <= j < |stack[i]| ==>
        stack[i][j] in contents);

    if i, j, v :| 0 <= i < stack.Length && 0 <= j < |stack[i]| && 
          stack[i][j] == (variable, v) {
      assert v == true || v == false;
    }
  }

  predicate occursInStack(variable : int) 
    reads this, stack;
    requires valid();
    requires validVariable(variable);
    requires size > 0;
    requires size == stack.Length;
    requires |stack[size-1]| > 0;
  {
    exists j :: 0 <= j < size && stack[j][0].0 == variable
  }

  predicate occursInContents(variable : int) 
    reads this, stack;
    requires valid();
    requires validVariable(variable);
    requires size > 0;
    requires size == stack.Length;
    requires |stack[size-1]| > 0;
  {
    exists x :: x in contents && x.0 == variable
  }

  lemma ifFull_containsAllVariables()
    requires valid();
    requires size > 0;
    requires size == stack.Length;
    requires |stack[size-1]| > 0;

    ensures forall v :: 0 <= v < size ==>
      occursInStack(v);

    ensures forall v :: 0 <= v < size ==>
      occursInContents(v);
  {
    var L: set<int>, R: set<int> := {}, RangeSet(0, size);
    var i := 0;
    CardinalityRangeSet(0, size);

    while (i < size)
      invariant 0 <= i <= size;
      invariant L == set j | 0 <= j < i :: stack[j][0].0;
      invariant forall v :: v in L ==> occursInStack(v);
      invariant forall v :: 0 <= v < size ==>
        v in L || v in R;
      /* invariant |L| + |R| == size;*/
      /* invariant |L| == i;*/
      invariant |R| == size - i;

      decreases size - i;
    {
        L, R := L + {stack[i][0].0}, R - {stack[i][0].0};
        i := i + 1;
    }

    assert forall v :: 0 <= v < size ==>
      v in L && occursInStack(v);

    forall v | 0 <= v < size
      ensures occursInContents(v);
    {
      assert occursInStack(v);
      var j :| 0 <= j < size && stack[j][0].0 == v;
      assert stack[j][0] in contents;
      assert occursInContents(v);
    }

    assert forall v :: 0 <= v < size ==>
      occursInContents(v);
  }

  method createNewLayer() 
    requires valid();
    requires size < stack.Length;
    requires size > 0 ==> |stack[size-1]| > 0;

    modifies this;

    ensures valid();
    ensures variablesCount == old(variablesCount);
    ensures contents == old(contents);
    ensures stack == old(stack);
    ensures size == old(size) + 1;
    ensures stack[size-1] == [];
  {
    size := size + 1;

    assert forall i :: 0 <= i < stack.Length ==>
      stack[i] == old(stack[i]);
  }
}
