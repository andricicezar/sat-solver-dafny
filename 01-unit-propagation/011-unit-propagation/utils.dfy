module Utils {
  method newInitializedSeq(n: int, d: int) returns (r : array<int>)
    requires 0 < n;
    ensures r.Length == n;
    ensures forall j :: 0 <= j < r.Length ==> r[j] == d;
    ensures fresh(r);
  {
    r := new int[n];

    var index : int := 0;
    while (index < n)
      invariant 0 <= index <= r.Length == n;
      invariant forall j :: 0 <= j < index ==> r[j] == d;    
      decreases n - index;
    {
      r[index] := d;
      index := index + 1;
    }
  }

  function method abs(literal: int) : int {
    if literal < 0 then - literal else literal
  }

  function method properClause(clause : seq<int>) : bool {
    forall literal :: (literal in clause) ==> literal != 0
  }

  function method properClauses(clauses : seq<seq<int>>) : bool {
    |clauses| > 0 &&
    forall clause :: (clause in clauses) ==> properClause(clause)
  }
  
  lemma prop_seq_predicate(q : int, abc : seq<int>) 
    requires forall j :: j in abc ==> 0 <= j < q;
    ensures forall j :: 0 <= j < |abc| ==> 0 <= abc[j] < q;
  {
    assert forall j :: 0 <= j < |abc| ==> 
              abc[j] in abc ==> 0 <= abc[j] < q;
  }

}
