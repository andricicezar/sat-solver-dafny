include "formula.dfy"

datatype SAT_UNSAT = SAT(tau:seq<int>) | UNSAT

class SATSolver {
  var formula : Formula;

  constructor(f' : Formula)
    requires f'.valid();
    ensures formula == f';
    ensures formula.valid();
  {
    formula := f';
  }

  method step(literal : int, value : bool) returns (result : SAT_UNSAT)
    requires formula.valid();
    requires 0 <= formula.stack.size < formula.stack.stack.Length;
    requires formula.stack.size > 0 ==> 
      |formula.stack.stack[formula.stack.size-1]| > 0;
    requires !formula.hasEmptyClause();
    requires !formula.isEmpty();
    requires formula.validLiteral(literal);
    requires formula.truthAssignment[formula.getVariableFromLiteral(literal)] == -1;
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1;

    modifies formula.truthAssignment, formula.stack, formula.stack.stack,
             formula.trueLiteralsCount, formula.falseLiteralsCount, 
             formula.satisfiedClauses;

    ensures old(formula) == formula;
    ensures formula.valid();
    ensures old(formula.stack) == formula.stack;
    ensures old(formula.stack.size) == formula.stack.size;
    ensures old(formula.stack.stack) == formula.stack.stack;
    ensures old(formula.stack.stack.Length) == formula.stack.stack.Length;
    ensures forall i :: 0 <= i < formula.stack.stack.Length ==>
      formula.stack.stack[i] == old(formula.stack.stack[i]);
    ensures old(formula.stack.contents) == formula.stack.contents; 
    ensures formula.stack.size > 0 ==>
            |formula.stack.stack[formula.stack.size-1]| > 0;

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);

    ensures result.SAT? ==> (
      var tau := formula.truthAssignment[..];
      var (variable, val) := formula.convertLVtoVI(literal, value);

      formula.isSatisfiableExtend(tau[variable := val])
    );

    ensures result.UNSAT? ==> (
      var tau := formula.truthAssignment[..];
      var (variable, val) := formula.convertLVtoVI(literal, value);

      !formula.isSatisfiableExtend(tau[variable := val])
    );

    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases *;
  {
    formula.newLayerOnStack();
    formula.setLiteral(literal, value);
    assert formula.countUnsetVariables(formula.truthAssignment[..]) < formula.countUnsetVariables(old(formula.truthAssignment[..]));
    result := solve();
    formula.undoLayerOnStack();

    assert formula.stack.contents == old(formula.stack.contents);
    if (formula.truthAssignment[..] != old(formula.truthAssignment[..])) {
      var i :| 0 <= i < formula.truthAssignment.Length && 
              formula.truthAssignment[i] != old(formula.truthAssignment[i]);

      var y := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));

      assert y in old(formula.stack.contents);
      assert y !in formula.stack.contents;
      assert formula.stack.contents == old(formula.stack.contents);
      assert false;
    }

    return result;
  }

  method solve() returns (result : SAT_UNSAT) 
    requires formula.valid();
    requires 0 <= formula.stack.size <= formula.stack.stack.Length;
    requires formula.stack.size > 0 ==> 
      |formula.stack.stack[formula.stack.size-1]| > 0;

    modifies formula.truthAssignment, formula.stack, formula.stack.stack,
             formula.trueLiteralsCount, formula.falseLiteralsCount, 
             formula.satisfiedClauses;

    ensures formula.valid();
    ensures old(formula.stack) == formula.stack;
    ensures old(formula.stack.size) == formula.stack.size;
    ensures old(formula.stack.stack) == formula.stack.stack;
    ensures old(formula.stack.stack.Length) == formula.stack.stack.Length;
    ensures forall i :: 0 <= i < formula.stack.stack.Length ==>
      formula.stack.stack[i] == old(formula.stack.stack[i]);
    ensures old(formula.stack.contents) == formula.stack.contents;
    ensures formula.stack.size > 0 ==> 
      |formula.stack.stack[formula.stack.size-1]| > 0;

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases *;
  {
    if (formula.hasEmptyClause()) {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }

    if (formula.isEmpty()) {
      formula.isEmpty_sastisfied();
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }

    formula.notEmptyNoEmptyClauses_stackNotFull();

    var literal := formula.chooseLiteral();

    result := step(literal, true);

    if (result.SAT?) { 
      return result;
    }
    
    result := step(literal, false);

    if (result.UNSAT?) {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(
        formula.truthAssignment[..],
        variable
      );
    }

    return result;
  }
}
