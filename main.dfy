include "01-unit-propagation/011-unit-propagation/solver.dfy"
include "input.dfy"
include "my_datatypes.dfy"

function method checkClauses(variablesCount: int, clauses : seq<seq<int>>) : bool{
  forall clause :: (clause in clauses) ==>
    forall literal :: (literal in clause) ==> (
      (literal < 0 && 0 < -literal <= variablesCount) ||
      (literal > 0 && 0 < literal <= variablesCount))
}

function method sortedClauses(clauses : seq<seq<int>>) : bool {
  forall clause :: (clause in clauses) ==>
    forall x, y :: 0 <= x < y < |clause| ==>
      clause[x] < clause[y]
}

method sort(variablesCount : int, clause : seq<int>) returns (newClause : seq<int>)
{
  var i := 0;
  newClause := [];
  var lastMin := -variablesCount-1;

  while (i < |clause|)
    invariant 0 <= i <= |clause|;
    decreases |clause|-i;
  {
    var j := 0;
    var min := variablesCount+1;
    while (j < |clause|)
      invariant 0 <= j <= |clause|;
      decreases |clause| - j;
    {
      if (lastMin < clause[j] < min) {
        min := clause[j];
      }
      j := j + 1;
    }

    newClause := newClause + [min];
    lastMin := min;
    i := i + 1;
  }

  /* print newClause, "\n";*/

}

method prepare(variablesCount : int, clauses : seq<seq<int>>) returns (newClauses : seq<seq<int>>)
{
  var k := 0;
  newClauses := [];

  while (k < |clauses|)
    invariant 0 <= k <= |clauses|;
    decreases |clauses| - k;
  {
    var newClause := sort(variablesCount, clauses[k]);
    newClauses := newClauses + [newClause];

    k := k + 1;
  }
}

method Main() 
  decreases *;
{
    var input := Input.getInput();
    
    match input {
        case Error(m) => print "Error: ", m;
        case Just((variablesCount, clauses)) =>
            var preparedClauses := prepare(variablesCount, clauses);
            if (variablesCount > 0 && |preparedClauses| > 0) {
              if (checkClauses(variablesCount, preparedClauses)) {
                if (sortedClauses(preparedClauses)) {
                  print "Starting ... \n";
                  var starttime := Input.getTimestamp();
                  var formula := new Formula(variablesCount, preparedClauses);
                  var solver := new SATSolver(formula);

                  var solution := solver.solve();
                  var totalTime : real := ((Input.getTimestamp()-starttime) as real)/1000.0;

                  match solution {
                    /* case SAT(x) => formula.render(x);*/
                    case SAT(x) => print("SAT!");
                    case UNSAT => print("UNSAT!");
                  }
                  print "Time to solve: ", totalTime, "s\n";
                } else {
                  print("Literals not in order");
                }
              } else {
                print("Literals not in [-variablesCount, variablesCount]-{0} interval");
              }

            }   
    }
}
