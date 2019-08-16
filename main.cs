// Dafny program main.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.3.0.10506
// Command Line Options: -errorLimit 5 -vcsCores 4 main.dfy file_input.cs main.cs
// main.dfy

function method checkClauses(variablesCount: int, clauses: seq<seq<int>>): bool
  decreases variablesCount, clauses
{
  forall clause: seq<int> :: 
    clause in clauses ==>
      forall literal: int :: 
        literal in clause ==>
          (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount)
}

function method sortedClauses(clauses: seq<seq<int>>): bool
  decreases clauses
{
  forall clause: seq<int> :: 
    clause in clauses ==>
      forall x: int, y: int :: 
        0 <= x < y < |clause| ==>
          clause[x] < clause[y]
}

method sort(variablesCount: int, clause: seq<int>) returns (newClause: seq<int>)
  decreases variablesCount, clause
{
  var i := 0;
  newClause := [];
  var lastMin := -variablesCount - 1;
  while i < |clause|
    invariant 0 <= i <= |clause|
    decreases |clause| - i
  {
    var j := 0;
    var min := variablesCount + 1;
    while j < |clause|
      invariant 0 <= j <= |clause|
      decreases |clause| - j
    {
      if lastMin < clause[j] < min {
        min := clause[j];
      }
      j := j + 1;
    }
    newClause := newClause + [min];
    lastMin := min;
    i := i + 1;
  }
}

method prepare(variablesCount: int, clauses: seq<seq<int>>) returns (newClauses: seq<seq<int>>)
  decreases variablesCount, clauses
{
  var k := 0;
  newClauses := [];
  while k < |clauses|
    invariant 0 <= k <= |clauses|
    decreases |clauses| - k
  {
    var newClause := sort(variablesCount, clauses[k]);
    newClauses := newClauses + [newClause];
    k := k + 1;
  }
}

method Main()
  decreases *
{
  var input := Input.getInput();
  match input {
    case Error(m) =>
      print ""Error: "", m;
    case Just((variablesCount, clauses)) =>
      var preparedClauses := prepare(variablesCount, clauses);
      if variablesCount > 0 && |preparedClauses| > 0 {
        if checkClauses(variablesCount, preparedClauses) {
          if sortedClauses(preparedClauses) {
            print ""Starting ... \n"";
            var starttime := Input.getTimestamp();
            var formula := new Formula(variablesCount, preparedClauses);
            var solver := new SATSolver(formula);
            var solution := solver.solve();
            var totalTime: real := (Input.getTimestamp() - starttime) as real / 1000.0;
            match solution {
              case SAT(x) =>
                print ""SAT!"";
              case UNSAT =>
                print ""UNSAT!"";
            }
            print ""Time to solve: "", totalTime, ""s\n"";
          } else {
            print ""Literals not in order"";
          }
        } else {
          print ""Literals not in [-variablesCount, variablesCount]-{0} interval"";
        }
      }
  }
}

predicate InRange(lo: int, hi: int, i: int)
  decreases lo, hi, i
{
  lo <= i < hi
}

predicate identity<T>(v: T)
{
  v == v
}

function RangeSet(lo: int, hi: int): set<int>
  decreases lo, hi
{
  set i: int {:trigger InRange(lo, hi, i)} | lo <= i < hi && InRange(lo, hi, i)
}

lemma CardinalityRangeSet(lo: int, hi: int)
  ensures |RangeSet(lo, hi)| == if lo >= hi then 0 else hi - lo
  decreases hi - lo
{
}

datatype SAT_UNSAT = SAT(tau: seq<int>) | UNSAT

class SATSolver {
  var formula: Formula

  constructor (f': Formula)
    requires f'.valid()
    ensures formula == f'
    ensures formula.valid()
    decreases f'
  {
    formula := f';
  }

  method step(literal: int, value: bool) returns (result: SAT_UNSAT)
    requires formula.valid()
    requires 0 <= formula.stack.size < formula.stack.stack.Length
    requires formula.stack.size > 0 ==> |formula.stack.stack[formula.stack.size - 1]| > 0
    requires !formula.hasEmptyClause()
    requires !formula.isEmpty()
    requires formula.validLiteral(literal)
    requires formula.truthAssignment[formula.getVariableFromLiteral(literal)] == -1
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1
    modifies formula.truthAssignment, formula.stack, formula.stack.stack, formula.trueLiteralsCount, formula.falseLiteralsCount, formula.satisfiedClauses
    ensures old(formula) == formula
    ensures formula.valid()
    ensures old(formula.stack) == formula.stack
    ensures old(formula.stack.size) == formula.stack.size
    ensures old(formula.stack.stack) == formula.stack.stack
    ensures old(formula.stack.stack.Length) == formula.stack.stack.Length
    ensures forall i: int :: 0 <= i < formula.stack.stack.Length ==> formula.stack.stack[i] == old(formula.stack.stack[i])
    ensures old(formula.stack.contents) == formula.stack.contents
    ensures formula.stack.size > 0 ==> |formula.stack.stack[formula.stack.size - 1]| > 0
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> var tau: seq<int> := formula.truthAssignment[..]; var (variable: int, val: int) := formula.convertLVtoVI(literal, value); formula.isSatisfiableExtend(tau[variable := val])
    ensures result.UNSAT? ==> var tau: seq<int> := formula.truthAssignment[..]; var (variable: int, val: int) := formula.convertLVtoVI(literal, value); !formula.isSatisfiableExtend(tau[variable := val])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases *
  {
    formula.newLayerOnStack();
    formula.setLiteral(literal, value);
    assert formula.countUnsetVariables(formula.truthAssignment[..]) < formula.countUnsetVariables(old(formula.truthAssignment[..]));
    result := solve();
    formula.undoLayerOnStack();
    assert formula.stack.contents == old(formula.stack.contents);
    if formula.truthAssignment[..] != old(formula.truthAssignment[..]) {
      ghost var i :| 0 <= i < formula.truthAssignment.Length && formula.truthAssignment[i] != old(formula.truthAssignment[i]);
      ghost var y := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
      assert y in old(formula.stack.contents);
      assert y !in formula.stack.contents;
      assert formula.stack.contents == old(formula.stack.contents);
      assert false;
    }
    return result;
  }

  method solve() returns (result: SAT_UNSAT)
    requires formula.valid()
    requires 0 <= formula.stack.size <= formula.stack.stack.Length
    requires formula.stack.size > 0 ==> |formula.stack.stack[formula.stack.size - 1]| > 0
    modifies formula.truthAssignment, formula.stack, formula.stack.stack, formula.trueLiteralsCount, formula.falseLiteralsCount, formula.satisfiedClauses
    ensures formula.valid()
    ensures old(formula.stack) == formula.stack
    ensures old(formula.stack.size) == formula.stack.size
    ensures old(formula.stack.stack) == formula.stack.stack
    ensures old(formula.stack.stack.Length) == formula.stack.stack.Length
    ensures forall i: int :: 0 <= i < formula.stack.stack.Length ==> formula.stack.stack[i] == old(formula.stack.stack[i])
    ensures old(formula.stack.contents) == formula.stack.contents
    ensures formula.stack.size > 0 ==> |formula.stack.stack[formula.stack.size - 1]| > 0
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures result.UNSAT? ==> !formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases *
  {
    if formula.hasEmptyClause() {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }
    if formula.isEmpty() {
      formula.isEmpty_sastisfied();
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }
    formula.notEmptyNoEmptyClauses_stackNotFull();
    var literal := formula.chooseLiteral();
    result := step(literal, true);
    if result.SAT? {
      return result;
    }
    result := step(literal, false);
    if result.UNSAT? {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(formula.truthAssignment[..], variable);
    }
    return result;
  }
}

module Input {

  import Parser = Parser

  import FileInput = FileInput

  import opened MyDatatypes = MyDatatypes
  function method getInput(): Maybe<(int, seq<seq<int>>)>
    reads *
    decreases {}
  {
    Parser.parseContent(FileInput.Reader.getContent()[0..])
  }

  function method getTimestamp(): int
  {
    FileInput.Reader.getTimestamp()
  }
}

module MyDatatypes {
  datatype Maybe<T> = Error(string) | Just(value: T)
}

class Formula extends DataStructures {
  constructor (variablesCount: int, clauses: seq<seq<int>>)
    requires 0 < variablesCount
    requires |clauses| > 0
    requires forall clause: seq<int> :: clause in clauses ==> forall literal: int :: literal in clause ==> (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount)
    requires forall clause: seq<int> :: clause in clauses ==> forall x: int, y: int :: 0 <= x < y < |clause| ==> clause[x] < clause[y]
    ensures valid()
    ensures fresh(stack)
    ensures fresh(stack.stack)
    ensures fresh(truthAssignment)
    ensures fresh(trueLiteralsCount)
    ensures fresh(falseLiteralsCount)
    ensures fresh(literalsCount)
    ensures fresh(satisfiedClauses)
    ensures fresh(positiveLiteralsToClauses)
    ensures fresh(negativeLiteralsToClauses)
    ensures stack.size == 0
    decreases variablesCount, clauses
  {
    this.variablesCount := variablesCount;
    this.clauses := clauses;
    this.stack := new Stack(variablesCount);
    new;
    ghost var clauses' := this.clauses;
    assert validClauses();
    ghost var stackStack' := this.stack.stack[..];
    ghost var stackSize' := this.stack.size;
    ghost var stackContents' := this.stack.contents;
    this.truthAssignment := Utils.newInitializedSeq(variablesCount, -1);
    ghost var truthAssignment' := truthAssignment[..];
    this.trueLiteralsCount := new int[|this.clauses|];
    this.falseLiteralsCount := new int[|this.clauses|];
    this.literalsCount := new int[|this.clauses|];
    this.satisfiedClauses := new bool[|clauses|];
    ghost var satisfiedClauses' := satisfiedClauses[..];
    positiveLiteralsToClauses := new seq<int>[variablesCount];
    negativeLiteralsToClauses := new seq<int>[variablesCount];
    assert this.clauses == clauses';
    assert validClauses();
    this.createTFLArrays();
    ghost var trueLiteralsCount' := trueLiteralsCount[..];
    ghost var falseLiteralsCount' := falseLiteralsCount[..];
    ghost var literalsCount' := literalsCount[..];
    assert validClauses();
    this.createPositiveLiteralsToClauses();
    assert validClauses();
    this.createNegativeLiteralsToClauses();
    assert truthAssignment[..] == truthAssignment';
    ghost var positiveLiteralsToClauses' := positiveLiteralsToClauses[..];
    ghost var negativeLiteralsToClauses' := negativeLiteralsToClauses[..];
    assert stackContents' == stack.contents;
    assert stackStack' == stack.stack[..];
    assert stackSize' == stack.size;
    assert validStack();
    assert forall x: int :: 0 <= x < truthAssignment.Length ==> truthAssignment[x] == -1;
    assert forall x: int :: 0 <= x < stack.stack.Length ==> |stack.stack[x]| == 0;
    assert validTruthAssignment();
    assert satisfiedClauses' == satisfiedClauses[..];
    assert satisfiedClauses.Length == |clauses|;
    this.createSatisfiedClausesArray();
    assert truthAssignment[..] == truthAssignment';
    assert trueLiteralsCount[..] == trueLiteralsCount';
    assert falseLiteralsCount[..] == falseLiteralsCount';
    assert literalsCount[..] == literalsCount';
    assert positiveLiteralsToClauses[..] == positiveLiteralsToClauses';
    assert negativeLiteralsToClauses[..] == negativeLiteralsToClauses';
  }

  method createTFLArrays()
    requires validReferences()
    requires validVariablesCount()
    requires validStack()
    requires validTruthAssignment()
    requires validClauses()
    requires literalsCount.Length == |clauses|
    requires trueLiteralsCount.Length == |clauses|
    requires falseLiteralsCount.Length == |clauses|
    requires forall value: int :: 0 <= value < truthAssignment.Length ==> truthAssignment[value] == -1
    modifies trueLiteralsCount, falseLiteralsCount, literalsCount
    ensures validLiteralsCount()
    ensures validTrueLiteralsCount(truthAssignment[..])
    ensures validFalseLiteralsCount(truthAssignment[..])
  {
    var i: int := 0;
    while i < |clauses|
      invariant 0 <= i <= |clauses|
      invariant forall j: int :: 0 <= j < i ==> literalsCount[j] == |clauses[j]|
      invariant forall j: int :: 0 <= j < i ==> trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j])
      invariant forall j: int :: 0 <= j < i ==> falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j])
      decreases |clauses| - i
    {
      literalsCount[i] := |clauses[i]|;
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      trueLiteralsCount[i] := 0;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      falseLiteralsCount[i] := 0;
      i := i + 1;
    }
  }

  predicate isSatisfied(truthAssignment: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads this
    decreases {this}, truthAssignment
  {
    forall cI: int :: 
      0 <= cI < |clauses| ==>
        isClauseSatisfied(truthAssignment, cI)
  }

  predicate isExtendingTau(tau: seq<int>, tau': seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validValuesTruthAssignment(tau')
    reads this
    decreases {this}, tau, tau'
  {
    forall i: int :: 
      0 <= i < |tau| &&
      tau[i] != -1 ==>
        tau[i] == tau'[i]
  }

  predicate isTauComplete(tau: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    reads this
    decreases {this}, tau
  {
    forall i: int :: 
      0 <= i < |tau| ==>
        tau[i] != -1
  }

  function getExtendedCompleteTau(tau: seq<int>): seq<int>
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires isSatisfiableExtend(tau)
    reads this
    ensures var tau': seq<int> := getExtendedCompleteTau(tau); validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau')
    decreases {this}, tau
  {
    var tau': seq<int> :| validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau');
    tau'
  }

  predicate isSatisfiableExtend(tau: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    reads this
    decreases {this}, tau
  {
    exists tau': seq<int> :: 
      validValuesTruthAssignment(tau') &&
      isTauComplete(tau') &&
      isExtendingTau(tau, tau') &&
      isSatisfied(tau')
  }

  lemma forVariableNotSatisfiableExtend_notSatisfiableExtend(tau: seq<int>, variable: int)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires !isSatisfiableExtend(tau[variable := 0])
    requires !isSatisfiableExtend(tau[variable := 1])
    ensures !isSatisfiableExtend(tau)
    decreases tau, variable
  {
  }

  lemma extensionSatisfiable_baseSatisfiable(tau: seq<int>, variable: int, value: int)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires value in [0, 1]
    requires tau[variable] == -1
    requires isSatisfiableExtend(tau[variable := value])
    ensures isSatisfiableExtend(tau)
    decreases tau, variable, value
  {
  }

  function method isUnitClause(index: int): bool
    requires validVariablesCount()
    requires validStack()
    requires validTruthAssignment()
    requires validClauses()
    requires validLiteralsCount()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < |clauses|
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount, falseLiteralsCount
    decreases {this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount, falseLiteralsCount}, index
  {
    trueLiteralsCount[index] == 0 &&
    literalsCount[index] - falseLiteralsCount[index] == 1
  }

  function method isEmptyClause(index: int): bool
    requires validVariablesCount()
    requires validStack()
    requires validTruthAssignment()
    requires validClauses()
    requires validLiteralsCount()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < |clauses|
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount, falseLiteralsCount
    decreases {this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount, falseLiteralsCount}, index
  {
    literalsCount[index] == falseLiteralsCount[index]
  }

  method createPositiveLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires positiveLiteralsToClauses.Length == variablesCount
    modifies positiveLiteralsToClauses
    ensures validPositiveLiteralsToClauses()
  {
    var variable := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: int :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
      decreases variablesCount - variable
    {
      positiveLiteralsToClauses[variable] := [];
      var clauseIndex := 0;
      while clauseIndex < |clauses|
        invariant 0 <= clauseIndex <= |clauses|
        invariant forall v: int :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
        invariant SeqPredicates.valuesBoundedBy(positiveLiteralsToClauses[variable], 0, |clauses|)
        invariant |positiveLiteralsToClauses[variable]| > 0 ==> positiveLiteralsToClauses[variable][|positiveLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant SeqPredicates.orderedAsc(positiveLiteralsToClauses[variable])
        invariant forall cI: int :: cI in positiveLiteralsToClauses[variable] ==> variable + 1 in clauses[cI]
        invariant forall cI: int :: 0 <= cI < clauseIndex ==> cI !in positiveLiteralsToClauses[variable] ==> variable + 1 !in clauses[cI]
        decreases |clauses| - clauseIndex
      {
        if variable + 1 in clauses[clauseIndex] {
          positiveLiteralsToClauses[variable] := positiveLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method createNegativeLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires negativeLiteralsToClauses.Length == variablesCount
    modifies negativeLiteralsToClauses
    ensures validNegativeLiteralsToClauses()
  {
    var variable := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: int :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
      decreases variablesCount - variable
    {
      negativeLiteralsToClauses[variable] := [];
      var clauseIndex := 0;
      while clauseIndex < |clauses|
        invariant 0 <= clauseIndex <= |clauses|
        invariant forall v: int :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
        invariant SeqPredicates.valuesBoundedBy(negativeLiteralsToClauses[variable], 0, |clauses|)
        invariant |negativeLiteralsToClauses[variable]| > 0 ==> negativeLiteralsToClauses[variable][|negativeLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant SeqPredicates.orderedAsc(negativeLiteralsToClauses[variable])
        invariant forall cI: int :: cI in negativeLiteralsToClauses[variable] ==> -variable - 1 in clauses[cI]
        invariant forall cI: int :: 0 <= cI < clauseIndex ==> cI !in negativeLiteralsToClauses[variable] ==> -variable - 1 !in clauses[cI]
        decreases |clauses| - clauseIndex
      {
        if -variable - 1 in clauses[clauseIndex] {
          negativeLiteralsToClauses[variable] := negativeLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method createSatisfiedClausesArray()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires validStack()
    requires validTruthAssignment()
    requires satisfiedClauses.Length == |clauses|
    requires forall value: int :: 0 <= value < truthAssignment.Length ==> truthAssignment[value] == -1
    modifies satisfiedClauses
    ensures validSatisfiedClauses(truthAssignment[..])
  {
    var i := 0;
    while i < |clauses|
      invariant 0 <= i <= |clauses|
      invariant forall j: int :: 0 <= j < i ==> satisfiedClauses[j] == isClauseSatisfied(truthAssignment[..], j)
      decreases |clauses| - i
    {
      assert validClause(clauses[i]);
      assert forall value: int :: 0 <= value < truthAssignment.Length ==> truthAssignment[value] == -1;
      assert forall literal: int :: literal in clauses[i] ==> getLiteralValue(truthAssignment[..], literal) == -1;
      assert isClauseSatisfied(truthAssignment[..], i) == false;
      satisfiedClauses[i] := false;
      i := i + 1;
    }
  }

  method newLayerOnStack()
    requires valid()
    requires 0 <= stack.size < stack.stack.Length
    requires stack.size > 0 ==> |stack.stack[stack.size - 1]| > 0
    modifies stack
    ensures valid()
    ensures stack.size == old(stack.size) + 1
    ensures 0 < stack.size <= stack.stack.Length
    ensures stack.stack == old(stack.stack)
    ensures forall i: int :: 0 <= i < stack.stack.Length ==> stack.stack[i] == old(stack.stack[i])
    ensures stack.contents == old(stack.contents)
  {
    stack.createNewLayer();
    assert stack.contents == old(stack.contents);
    assert old(truthAssignment[..]) == truthAssignment[..];
  }

  method undoLayerOnStack()
    requires valid()
    requires 0 < stack.size <= stack.stack.Length
    requires |stack.stack[stack.size - 1]| > 0
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount, falseLiteralsCount, satisfiedClauses
    ensures valid()
    ensures stack.size == old(stack.size) - 1
    ensures stack.stack == old(stack.stack)
    ensures 0 <= stack.size < stack.stack.Length
    ensures forall i: int :: 0 <= i < stack.stack.Length && i != stack.size ==> stack.stack[i] == old(stack.stack[i])
    ensures |stack.stack[stack.size]| == 0
    ensures forall x: (int, bool) :: x in old(stack.contents) && x !in old(stack.stack[stack.size - 1]) ==> x in stack.contents
    ensures forall x: (int, bool) :: x in old(stack.stack[stack.size - 1]) ==> x !in stack.contents
    ensures stack.contents == old(stack.contents) - old(stack.getLastLayer())
    ensures stack.size > 0 ==> |stack.stack[stack.size - 1]| > 0
  {
    var k := 0;
    var layer := stack.stack[stack.size - 1];
    stack.stack[stack.size - 1] := [];
    stack.size := stack.size - 1;
    while k < |layer|
      invariant 0 <= k <= |layer|
      invariant forall k': int :: 0 <= k' < k ==> layer[k'] !in stack.contents
      invariant forall k': int :: k <= k' < |layer| ==> layer[k'] in stack.contents
      invariant 0 <= stack.size < stack.stack.Length
      invariant old(stack.variablesCount) == stack.variablesCount
      invariant old(stack.size) - 1 == stack.size
      invariant old(stack.stack) == stack.stack
      invariant forall i: int :: 0 <= i < stack.size ==> old(stack.stack[i]) == stack.stack[i]
      invariant forall i: int :: 0 <= i < stack.size ==> forall j: (int, bool) :: j in stack.stack[i] ==> j in stack.contents
      invariant forall j: (int, bool) :: j in stack.contents ==> j in old(stack.contents)
      invariant k > 0 ==> stack.contents == old(stack.contents) - set j: (int, bool) {:trigger j in layer[..k]} | j in layer[..k]
      invariant forall i: int :: stack.size <= i < stack.stack.Length ==> stack.stack[i] == []
      invariant forall j: int :: 0 <= j < truthAssignment.Length && truthAssignment[j] != -1 ==> (j, convertIntToBool(truthAssignment[j])) in stack.contents
      invariant forall j: int :: 0 <= j < k ==> truthAssignment[layer[j].0] == -1
      invariant forall j: int :: 0 <= j < truthAssignment.Length && truthAssignment[j] == -1 ==> (j, false) !in stack.contents && (j, true) !in stack.contents
      invariant truthAssignment.Length == variablesCount
      invariant forall i: int :: 0 <= i < truthAssignment.Length ==> -1 <= truthAssignment[i] <= 1
      invariant forall cI: int :: 0 <= cI < |clauses| ==> trueLiteralsCount[cI] == countTrueLiterals(truthAssignment[..], clauses[cI])
      invariant forall cI: int :: 0 <= cI < |clauses| ==> falseLiteralsCount[cI] == countFalseLiterals(truthAssignment[..], clauses[cI])
      invariant forall cI: int :: 0 <= cI < |clauses| ==> satisfiedClauses[cI] == isClauseSatisfied(truthAssignment[..], cI)
      decreases |layer| - k
      modifies stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, satisfiedClauses
    {
      var x := layer[k];
      k := k + 1;
      var (variable, value) := x;

      ghost var previousTau := truthAssignment[..];
      truthAssignment[variable] := -1;
      ghost var newTau := truthAssignment[..];
      assert validValuesTruthAssignment(newTau);
      assert forall i: int :: 0 <= i < |previousTau| && i != variable ==> previousTau[i] == newTau[i];
      assert previousTau[variable] in {0, 1} && newTau[variable] == -1;
      stack.contents := stack.contents - {x};
      var positivelyImpactedClauses := positiveLiteralsToClauses[variable];
      var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
      if !value {
        negativelyImpactedClauses := positiveLiteralsToClauses[variable];
        positivelyImpactedClauses := negativeLiteralsToClauses[variable];
      }
      assert SeqPredicates.valuesBoundedBy(positivelyImpactedClauses, 0, |clauses|);
      assert SeqPredicates.valuesBoundedBy(negativelyImpactedClauses, 0, |clauses|);
      undoImpactedClauses_TFSArraysModified(previousTau, newTau, variable, positivelyImpactedClauses, negativelyImpactedClauses);
      var i := 0;
      while i < |positivelyImpactedClauses|
        invariant 0 <= i <= |positivelyImpactedClauses|
        invariant forall i': int :: 0 <= i' < |clauses| && i' !in positivelyImpactedClauses ==> trueLiteralsCount[i'] == countTrueLiterals(newTau, clauses[i'])
        invariant forall i': int :: 0 <= i' < i ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']])
        invariant forall i': int :: i <= i' < |positivelyImpactedClauses| ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']])
        invariant forall i': int :: 0 <= i' < |clauses| && i' !in positivelyImpactedClauses ==> satisfiedClauses[i'] == isClauseSatisfied(newTau, i')
        invariant forall i': int :: 0 <= i' < i ==> satisfiedClauses[positivelyImpactedClauses[i']] == isClauseSatisfied(newTau, positivelyImpactedClauses[i'])
        invariant forall i': int :: i <= i' < |positivelyImpactedClauses| ==> satisfiedClauses[positivelyImpactedClauses[i']] == isClauseSatisfied(previousTau, positivelyImpactedClauses[i'])
        decreases |positivelyImpactedClauses| - i
        modifies trueLiteralsCount, satisfiedClauses
      {
        var clauseIndex := positivelyImpactedClauses[i];
        var clause := clauses[clauseIndex];
        assert validClause(clause);
        unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
        trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;
        if trueLiteralsCount[clauseIndex] == 0 {
          countTrueLiterals0_noLiteralsTrue(newTau, clause);
          satisfiedClauses[clauseIndex] := false;
        } else {
          countTrueLiteralsX_existsTrueLiteral(newTau, clause);
        }
        i := i + 1;
      }
      i := 0;
      while i < |negativelyImpactedClauses|
        invariant 0 <= i <= |negativelyImpactedClauses|
        invariant forall i': int :: 0 <= i' < i ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': int :: i <= i' < |negativelyImpactedClauses| ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': int :: 0 <= i' < |clauses| && i' !in negativelyImpactedClauses ==> falseLiteralsCount[i'] == countFalseLiterals(newTau, clauses[i'])
        decreases |negativelyImpactedClauses| - i
        modifies falseLiteralsCount
      {
        var clauseIndex := negativelyImpactedClauses[i];
        unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
        falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
        i := i + 1;
      }
    }
  }

  method setVariable(variable: int, value: bool)
    requires valid()
    requires validVariable(variable)
    requires truthAssignment[variable] == -1
    requires 0 < stack.size <= stack.stack.Length
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount, satisfiedClauses, falseLiteralsCount
    ensures valid()
    ensures value == false ==> truthAssignment[variable] == 0
    ensures value == true ==> truthAssignment[variable] == 1
    ensures value == false ==> old(truthAssignment[..][variable := 0]) == truthAssignment[..]
    ensures value == true ==> old(truthAssignment[..][variable := 1]) == truthAssignment[..]
    ensures stack.size == old(stack.size)
    ensures stack.stack == old(stack.stack)
    ensures 0 < stack.size <= stack.stack.Length
    ensures |stack.stack[stack.size - 1]| == |old(stack.stack[stack.size - 1])| + 1
    ensures stack.contents == old(stack.contents) + {(variable, value)}
    ensures forall i: int :: 0 <= i < stack.size - 1 ==> stack.stack[i] == old(stack.stack[i])
    ensures countUnsetVariables(truthAssignment[..]) + 1 == old(countUnsetVariables(truthAssignment[..]))
    decreases variable, value
  {
    ghost var oldTau := truthAssignment[..];
    var el := (variable, value);
    var iL := stack.size - 1;
    stack.variableNotInContents_variableNotInStack(variable);
    stack.stack[iL] := stack.stack[iL] + [el];
    stack.contents := stack.contents + {el};
    if value {
      truthAssignment[variable] := 1;
    } else {
      truthAssignment[variable] := 0;
    }
    ghost var newTau := truthAssignment[..];
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
    ghost var elI := |stack.stack[iL]| - 1;
    assert stack.contents - old(stack.contents) == {el};
    assert forall i: int :: 0 <= i < iL ==> old(stack.stack[i]) == stack.stack[i];
    assert old(stack.stack[iL]) == stack.stack[iL][..elI];
    assert stack.stack[iL][|stack.stack[iL]| - 1] == el;
    assert validStack();
    var trueLiteral := variable + 1;
    var falseLiteral := -variable - 1;
    if !value {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    var i := 0;
    var impactedClauses := positiveLiteralsToClauses[variable];
    var impactedClauses' := negativeLiteralsToClauses[variable];
    if !value {
      impactedClauses := negativeLiteralsToClauses[variable];
      impactedClauses' := positiveLiteralsToClauses[variable];
    }
    clausesNotImpacted_TFArraysSame(oldTau, newTau, variable, impactedClauses, impactedClauses');
    Utils.prop_seq_predicate(|clauses|, impactedClauses);
    assert value ==> validPositiveLiteralToClause(variable, impactedClauses);
    assert !value ==> validNegativeLiteralsToClause(variable, impactedClauses);
    while i < |impactedClauses|
      invariant 0 <= i <= |impactedClauses|
      invariant forall j: int :: 0 <= j < |clauses| && j !in impactedClauses ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j])
      invariant forall cI: int :: 0 <= cI < |clauses| && cI !in impactedClauses ==> satisfiedClauses[cI] == isClauseSatisfied(newTau, cI) == old(satisfiedClauses[cI])
      invariant forall j: int :: 0 <= j < i ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(newTau, clauses[impactedClauses[j]])
      invariant forall j: int :: i <= j < |impactedClauses| ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(oldTau, clauses[impactedClauses[j]])
      invariant forall j: int :: 0 <= j < i ==> satisfiedClauses[impactedClauses[j]] == isClauseSatisfied(newTau, impactedClauses[j])
      decreases |impactedClauses| - i
      modifies trueLiteralsCount, satisfiedClauses
    {
      var clauseIndex := impactedClauses[i];
      setVariable_countTrueLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;
      satisfiedClauses[clauseIndex] := true;
      assert trueLiteral in clauses[clauseIndex] && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);
      i := i + 1;
    }
    assert validTrueLiteralsCount(newTau);
    assert validSatisfiedClauses(newTau);
    var i' := 0;
    Utils.prop_seq_predicate(|clauses|, impactedClauses');
    assert value ==> validNegativeLiteralsToClause(variable, impactedClauses');
    assert !value ==> validPositiveLiteralToClause(variable, impactedClauses');
    while i' < |impactedClauses'|
      invariant 0 <= i' <= |impactedClauses'|
      invariant forall j: int :: 0 <= j < |clauses| && j !in impactedClauses' ==> falseLiteralsCount[j] == countFalseLiterals(newTau, clauses[j])
      invariant forall j: int :: 0 <= j < i' ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(newTau, clauses[impactedClauses'[j]])
      invariant forall j: int :: i' <= j < |impactedClauses'| ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(oldTau, clauses[impactedClauses'[j]])
      decreases |impactedClauses'| - i'
      modifies falseLiteralsCount
    {
      var clauseIndex := impactedClauses'[i'];
      setVariable_countFalseLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;
      i' := i' + 1;
    }
    assert validReferences();
    assert validVariablesCount();
    assert validClauses();
    assert validStack();
    assert validTruthAssignment();
    assert validSatisfiedClauses(truthAssignment[..]);
    assert validTrueLiteralsCount(truthAssignment[..]);
    assert validFalseLiteralsCount(truthAssignment[..]);
    assert validLiteralsCount();
    assert validPositiveLiteralsToClauses();
    assert validNegativeLiteralsToClauses();
  }

  function method hasEmptyClause(): bool
    requires valid()
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures hasEmptyClause() == true ==> exists i: int :: 0 <= i < |clauses| && falseLiteralsCount[i] == literalsCount[i]
    ensures hasEmptyClause() == false ==> forall i: int :: 0 <= i < |clauses| ==> falseLiteralsCount[i] < literalsCount[i]
    decreases {this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: int :: 0 <= i < |clauses| && falseLiteralsCount[i] == literalsCount[i] then
      var i: int :| 0 <= i < |clauses| && falseLiteralsCount[i] == literalsCount[i];
      true
    else
      false
  }

  function method isEmpty(): bool
    requires valid()
    requires !hasEmptyClause()
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures isEmpty() == true ==> forall i: int :: 0 <= i < |clauses| ==> trueLiteralsCount[i] > 0
    ensures isEmpty() == false ==> exists i: int :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0
    decreases {this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: int :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0 then
      var i: int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0;
      false
    else
      true
  }

  lemma notEmptyNoEmptyClauses_stackNotFull()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires stack.size > 0 ==> |stack.stack[stack.size - 1]| > 0
    ensures stack.size < stack.stack.Length
  {
  }

  lemma allVariablesSet_done()
    requires valid()
    requires forall v: int :: validVariable(v) ==> isVariableSet(truthAssignment[..], v)
    ensures hasEmptyClause() || isEmpty()
  {
  }

  lemma tauFullClauseNotEmpty_clauseIsSatisfied(cI: int)
    requires valid()
    requires 0 <= cI < |clauses|
    requires validClause(clauses[cI])
    requires forall x: int :: x in clauses[cI] ==> isVariableSet(truthAssignment[..], getVariableFromLiteral(x))
    requires falseLiteralsCount[cI] < literalsCount[cI]
    ensures trueLiteralsCount[cI] > 0
    decreases cI
  {
  }

  lemma /*{:_induction clause, truthAssignment}*/ existsTrueLiteral_countTrueLiteralsPositive(clause: seq<int>, truthAssignment: seq<int>)
    requires valid()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires exists x: int :: x in clause && getLiteralValue(truthAssignment, x) == 1
    ensures countTrueLiterals(truthAssignment, clause) > 0
    decreases clause, truthAssignment
  {
  }

  method chooseLiteral() returns (x: int)
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    ensures valid()
    ensures validLiteral(x)
    ensures truthAssignment[getVariableFromLiteral(x)] == -1
    ensures getLiteralValue(truthAssignment[..], x) == -1
  {
    var i: int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0;
    assert validClause(clauses[i]);
    notDone_literalsToSet(i);
    var literal :| literal in clauses[i] && truthAssignment[getVariableFromLiteral(literal)] == -1;
    return literal;
  }

  method setLiteral(literal: int, value: bool)
    requires valid()
    requires validLiteral(literal)
    requires getLiteralValue(truthAssignment[..], literal) == -1
    requires 0 < stack.size <= stack.stack.Length
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount, falseLiteralsCount, satisfiedClauses
    ensures valid()
    ensures 0 < stack.size <= stack.stack.Length
    ensures stack.size == old(stack.size)
    ensures stack.stack == old(stack.stack)
    ensures |stack.stack[stack.size - 1]| > 0
    ensures forall i: int :: 0 <= i < stack.stack.Length && i != stack.size - 1 ==> stack.stack[i] == old(stack.stack[i])
    ensures forall x: (int, bool) :: x in old(stack.contents) ==> x in stack.contents
    ensures stack.contents == old(stack.contents) + stack.getLastLayer()
    ensures countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]))
    ensures ghost var tau: seq<int> := old(truthAssignment[..]); var (variable: int, val: int) := convertLVtoVI(literal, value); ghost var tau': seq<int> := tau[variable := val]; isSatisfiableExtend(tau') <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..])
  {
    ghost var tau := truthAssignment[..];
    var (vari, val) := convertLVtoVI(literal, value);

    ghost var tau' := tau[vari := val];
    var variable := getVariableFromLiteral(literal);
    var value' := if literal > 0 then value else !value;
    setVariable(variable, value');
    assert tau' == truthAssignment[..];
    var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
    var k := 0;
    ghost var unsetVariablesCount := countUnsetVariables(truthAssignment[..]);
    assert unsetVariablesCount + 1 == old(countUnsetVariables(truthAssignment[..]));
    assert unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]));
    while k < |negativelyImpactedClauses|
      invariant 0 <= k <= |negativelyImpactedClauses|
      invariant valid()
      invariant 0 < stack.size <= stack.stack.Length
      invariant stack.size == old(stack.size)
      invariant stack.stack == old(stack.stack)
      invariant |stack.stack[stack.size - 1]| > 0
      invariant forall i: int :: 0 <= i < stack.size - 1 ==> stack.stack[i] == old(stack.stack[i])
      invariant forall x: (int, bool) :: x in old(stack.contents) ==> x in stack.contents
      invariant unsetVariablesCount == countUnsetVariables(truthAssignment[..])
      invariant unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]))
      invariant isSatisfiableExtend(tau') <==> isSatisfiableExtend(truthAssignment[..])
      decreases |negativelyImpactedClauses| - k
    {
      var clauseIndex := negativelyImpactedClauses[k];
      var clause := clauses[clauseIndex];
      assert validClause(clause);
      if trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex] {
        unitClause_existsUnsetLiteral(clauseIndex);
        var literal :| literal in clause && truthAssignment[getVariableFromLiteral(literal)] == -1;
        var (v', val') := convertLVtoVI(literal, true);

        ghost var tau'' := truthAssignment[..];
        unitClauseLiteralFalse_tauNotSatisfiable(tau'', clauseIndex, literal);
        setLiteral(literal, true);
        assert isSatisfiableExtend(tau''[v' := val']) <==> isSatisfiableExtend(truthAssignment[..]);
        if isSatisfiableExtend(truthAssignment[..]) {
          extensionSatisfiable_baseSatisfiable(tau'', v', val');
        } else {
          forVariableNotSatisfiableExtend_notSatisfiableExtend(tau'', v');
        }
        assert !isSatisfiableExtend(tau'') <==> !isSatisfiableExtend(truthAssignment[..]);
        unsetVariablesCount := countUnsetVariables(truthAssignment[..]);
        assert unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]));
      }
      k := k + 1;
    }
    assert unsetVariablesCount == countUnsetVariables(truthAssignment[..]);
    assert unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]));
  }

  lemma unitClause_existsUnsetLiteral(clauseIndex: int)
    requires valid()
    requires 0 <= clauseIndex < |clauses|
    requires validClause(clauses[clauseIndex])
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex]
    ensures exists literal: int :: literal in clauses[clauseIndex] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
  }

  method render(truthAssignment: seq<int>)
    requires valid()
    requires validValuesTruthAssignment(truthAssignment)
    requires |truthAssignment| == variablesCount
    decreases truthAssignment
  {
    var clauseIndex := 0;
    print ""Solution:\n"", truthAssignment, ""\n\nClauses:\n"";
    while clauseIndex < |clauses|
      invariant 0 <= clauseIndex <= |clauses|
      decreases |clauses| - clauseIndex
    {
      var clause := clauses[clauseIndex];
      assert validClause(clause);
      var literalIndex := 0;
      while literalIndex < |clause|
        decreases |clause| - literalIndex
      {
        var literal := clause[literalIndex];
        assert validLiteral(literal);
        print literal;
        assert 0 <= Utils.abs(literal) - 1 < variablesCount;
        if literal < 0 && truthAssignment[-literal - 1] == 0 {
          print '*';
        } else if literal > 0 && truthAssignment[literal - 1] == 1 {
          print '*';
        }
        print ' ';
        literalIndex := literalIndex + 1;
      }
      print '\n';
      clauseIndex := clauseIndex + 1;
    }
  }

  lemma hasEmptyClause_notSatisfiable()
    requires valid()
    requires hasEmptyClause()
    ensures !isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex: int)
    requires valid()
    requires 0 <= clauseIndex < |clauses|
    requires falseLiteralsCount[clauseIndex] == literalsCount[clauseIndex]
    requires validClause(clauses[clauseIndex])
    ensures forall literal: int :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment[..], literal) == 0
    decreases clauseIndex
  {
  }

  lemma isEmpty_sastisfied()
    requires valid()
    requires !hasEmptyClause()
    requires isEmpty()
    ensures isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma partialTauSatisfied_isSatisfiableExtend(tau: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClauses()
    requires isSatisfied(tau)
    ensures isSatisfiableExtend(tau)
    decreases countUnsetVariables(tau)
  {
  }

  lemma unitClause_allFalseExceptLiteral(truthAssignment: seq<int>, clauseIndex: int, literal: int)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires 0 <= clauseIndex < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|
    requires literal in clauses[clauseIndex]
    requires getLiteralValue(truthAssignment, literal) == -1
    requires forall literal: int :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment, literal) != 1
    ensures forall literal': int :: literal' in clauses[clauseIndex] && literal' != literal ==> getLiteralValue(truthAssignment, literal') != -1
    decreases truthAssignment, clauseIndex, literal
  {
  }

  lemma unitClauseLiteralFalse_tauNotSatisfiable(truthAssignment: seq<int>, clauseIndex: int, literal: int)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires validLiteralsCount()
    requires 0 <= clauseIndex < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex]
    requires truthAssignment[getVariableFromLiteral(literal)] == -1
    requires literal in clauses[clauseIndex]
    ensures var (variable: int, value: int) := convertLVtoVI(literal, false); !isSatisfiableExtend(truthAssignment[variable := value])
    decreases truthAssignment, clauseIndex, literal
  {
  }
}

module Parser {

  import opened MyDatatypes = MyDatatypes
  function method skipLine(content: string): string
    ensures |content| > 0 ==> |skipLine(content)| < |content|
    decreases |content|
  {
    if |content| == 0 then
      content
    else if content[0] == '\n' then
      content[1..]
    else
      skipLine(content[1..])
  }

  lemma /*{:_induction content}*/ prop_skipWhiteSpaces(content: string)
    ensures |skipWhiteSpaces(content)| <= |content|
    decreases content
  {
  }

  function method skipWhiteSpaces(content: string): string
    decreases |content|
  {
    if |content| == 0 then
      content
    else if content[0] == ' ' then
      skipWhiteSpaces(content[1..])
    else if content[0] == '\n' then
      skipWhiteSpaces(content[1..])
    else
      content
  }

  function method isDigit(chr: char): bool
    decreases chr
  {
    '0' <= chr <= '9'
  }

  function method toInt(chr: char): int
    requires isDigit(chr)
    decreases chr
  {
    chr as int - '0' as int
  }

  lemma /*{:_induction content}*/ prop_extractDigits(content: string)
    ensures |content| == |extractDigits(content).0| + |extractDigits(content).1|
    decreases content
  {
  }

  function method extractDigits(content: string): (seq<int>, string)
    decreases |content|
  {
    if |content| == 0 then
      ([], content)
    else if isDigit(content[0]) then
      var (h: seq<int>, tail: string) := extractDigits(content[1..]);
      ([toInt(content[0])] + h, tail)
    else
      ([], content)
  }

  function method joinInts(number: int, ints: seq<int>): int
    decreases |ints|
  {
    if |ints| == 0 then
      number
    else
      joinInts(number * 10 + ints[0], ints[1..])
  }

  lemma prop_getNextNumber(content: string)
    requires getNextNumber(content).Just?
    ensures |getNextNumber(content).value.1| < |content|
    decreases content
  {
  }

  function method getNextNumber(content: string): Maybe<(int, string)>
    decreases |content|
  {
    if |content| == 0 then
      Error(""content finished unexpectatly"")
    else if content[0] == '-' then
      var (digits: seq<int>, newContent: string) := extractDigits(content[1..]);
      prop_extractDigits(content[1..]);
      if |digits| == 0 then
        Error(""only alpha characters ahead, no numbers after -"")
      else
        var number: int := joinInts(0, digits); assert |newContent| < |content|; Just((-number, newContent))
    else
      var (digits: seq<int>, newContent: string) := extractDigits(content); prop_extractDigits(content); if |digits| == 0 then Error(""only alpha characters ahead, no numbers"") else var number: int := joinInts(0, digits); assert |newContent| < |content|; Just((number, newContent))
  }

  function method extractNumbers(content: string): (seq<int>, string)
    decreases |content|
  {
    prop_skipWhiteSpaces(content);
    var content': string := skipWhiteSpaces(content);
    match getNextNumber(content')
    case Error(_) =>
      ([], content')
    case Just((number, content'')) =>
      prop_getNextNumber(content');
      prop_skipWhiteSpaces(content'');
      var content''' := skipWhiteSpaces(content'');
      assert |content'''| < |content'| <= |content|;
      var (fst, snd) := extractNumbers(content''');
      ([number] + fst, snd)
  }

  function method getNextClause(numbers: seq<int>): Maybe<(seq<int>, seq<int>)>
    decreases |numbers|
  {
    if |numbers| == 0 then
      Error(""no 0 there"")
    else if numbers[0] == 0 then
      Just(([], numbers[1..]))
    else
      var head: seq<int> := [numbers[0]]; match getNextClause(numbers[1..]) case Error(m) => Error(m) case Just((tail, numbers)) => Just((head + tail, numbers))
  }

  function method getClauses(clausesCount: int, numbers: seq<int>): Maybe<(seq<seq<int>>, seq<int>)>
    decreases clausesCount, |numbers|
  {
    if clausesCount <= 0 || |numbers| == 0 then
      Just(([], numbers))
    else
      match getNextClause(numbers) case Error(m) => Error(m) case Just((clause, numbers)) => match getClauses(clausesCount - 1, numbers) case Error(m) => Error(m) case Just((clauses, numbers)) => Just(([clause] + clauses, numbers))
  }

  function method getToInput(content: string): Maybe<string>
    decreases |content|
  {
    prop_skipWhiteSpaces(content);
    var content: seq<char> := skipWhiteSpaces(content);
    if |content| == 0 then
      Error(""nothing found"")
    else if content[0] == 'c' then
      getToInput(skipLine(content))
    else if content[0] == 'p' then
      var content: seq<char> := skipWhiteSpaces(content[1..]);
      if |content| < 3 then
        Error(""input not correctly formated"")
      else
        Just(skipWhiteSpaces(content[3..]))
    else
      Error(""invalid symbol"")
  }

  function method parseContent(content: string): Maybe<(int, seq<seq<int>>)>
    decreases content
  {
    match getToInput(content)
    case Error(m) =>
      Error(m)
    case Just(content) =>
      match getNextNumber(content)
      case Error(m) =>
        Error(m)
      case Just((variablesCount, content)) =>
        match getNextNumber(skipWhiteSpaces(content))
        case Error(m) =>
          Error(m)
        case Just((clausesCount, content)) =>
          var (numbers, _) := extractNumbers(content);
          match getClauses(clausesCount, numbers)
          case Error(m) =>
            Error(m)
          case Just((clauses, content)) =>
            Just((variablesCount, clauses))
  }
}

module {:extern ""FileInput""} FileInput {
  class {:extern ""Reader""} Reader {
    static function method {:extern ""getContent""} getContent(): array<char>

    static function method {:extern ""getTimestamp""} getTimestamp(): int
  }
}

trait DataStructures {
  var variablesCount: int
  var clauses: seq<seq<int>>
  var stack: Stack
  var truthAssignment: array<int>
  var satisfiedClauses: array<bool>
  var trueLiteralsCount: array<int>
  var falseLiteralsCount: array<int>
  var literalsCount: array<int>
  var positiveLiteralsToClauses: array<seq<int>>
  var negativeLiteralsToClauses: array<seq<int>>

  predicate validVariablesCount()
    reads this
    decreases {this}
  {
    variablesCount > 0
  }

  predicate validClauses()
    requires validVariablesCount()
    reads this
    decreases {this}
  {
    |clauses| > 0 &&
    forall clause: seq<int> :: 
      clause in clauses ==>
        validClause(clause)
  }

  predicate validClause(clause: seq<int>)
    requires validVariablesCount()
    reads this
    decreases {this}, clause
  {
    (forall x: int, y: int :: 
      0 <= x < y < |clause| ==>
        clause[x] < clause[y]) &&
    forall literal: int :: 
      literal in clause ==>
        validLiteral(literal)
  }

  predicate validLiteral(literal: int)
    requires validVariablesCount()
    reads this
    decreases {this}, literal
  {
    if literal == 0 then
      false
    else if -variablesCount <= literal <= variablesCount then
      true
    else
      false
  }

  predicate validVariable(variable: int)
    requires validVariablesCount()
    reads this
    decreases {this}, variable
  {
    0 <= variable < variablesCount
  }

  predicate validStack()
    requires validVariablesCount()
    reads this, stack, stack.stack
    decreases {this, stack, stack.stack}
  {
    stack.valid() &&
    stack.variablesCount == this.variablesCount
  }

  function convertIntToBool(x: int): bool
    decreases x
  {
    if x == 0 then
      false
    else
      true
  }

  predicate validValuesTruthAssignment(truthAssignment: seq<int>)
    requires validVariablesCount()
    reads this
    decreases {this}, truthAssignment
  {
    |truthAssignment| == variablesCount &&
    forall i: int :: 
      0 <= i < |truthAssignment| ==>
        -1 <= truthAssignment[i] <= 1
  }

  predicate validTruthAssignment()
    requires validVariablesCount()
    requires validStack()
    reads this, stack, stack.stack, truthAssignment
    decreases {this, stack, stack.stack, truthAssignment}
  {
    validValuesTruthAssignment(truthAssignment[..]) &&
    (forall i: int :: 
      0 <= i < truthAssignment.Length &&
      truthAssignment[i] != -1 ==>
        (i, convertIntToBool(truthAssignment[i])) in stack.contents) &&
    forall i: int :: 
      0 <= i < truthAssignment.Length &&
      truthAssignment[i] == -1 ==>
        (i, false) !in stack.contents &&
        (i, true) !in stack.contents
  }

  predicate validSatisfiedClauses(truthAssignment: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads this, stack, stack.stack, satisfiedClauses
    decreases {this, stack, stack.stack, satisfiedClauses}, truthAssignment
  {
    satisfiedClauses.Length == |clauses| &&
    forall i: int :: 
      0 <= i < satisfiedClauses.Length ==>
        satisfiedClauses[i] == isClauseSatisfied(truthAssignment, i)
  }

  predicate isClauseSatisfied(truthAssignment: seq<int>, clauseIndex: int)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires 0 <= clauseIndex < |clauses|
    reads this
    decreases {this}, truthAssignment, clauseIndex
  {
    assert validClause(clauses[clauseIndex]);
    exists literal: int :: 
      literal in clauses[clauseIndex] &&
      getLiteralValue(truthAssignment, literal) == 1
  }

  function method convertLVtoVI(literal: int, value: bool): (int, int)
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(convertLVtoVI(literal, value).0)
    ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal)
    ensures convertLVtoVI(literal, value).1 in [0, 1]
    decreases {this}, literal, value
  {
    var variable: int := getVariableFromLiteral(literal);
    var v: int := if value then 1 else 0;
    var val: int := if literal < 0 then 1 - v else v;
    (variable, val)
  }

  function method getVariableFromLiteral(literal: int): int
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(getVariableFromLiteral(literal))
    decreases {this}, literal
  {
    Utils.abs(literal) - 1
  }

  function getLiteralValue(truthAssignment: seq<int>, literal: int): int
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validLiteral(literal)
    reads this
    decreases {this}, truthAssignment, literal
  {
    var variable: int := Utils.abs(literal) - 1;
    if truthAssignment[variable] == -1 then
      -1
    else if literal < 0 then
      1 - truthAssignment[variable]
    else
      truthAssignment[variable]
  }

  predicate validTrueLiteralsCount(truthAssignment: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads this, trueLiteralsCount
    decreases {this, trueLiteralsCount}, truthAssignment
  {
    trueLiteralsCount.Length == |clauses| &&
    forall i: int :: 
      0 <= i < |clauses| ==>
        0 <= trueLiteralsCount[i] == countTrueLiterals(truthAssignment, clauses[i])
  }

  function countUnsetVariables(truthAssignment: seq<int>): int
    ensures 0 <= countUnsetVariables(truthAssignment) <= |truthAssignment|
    decreases truthAssignment
  {
    if |truthAssignment| == 0 then
      0
    else
      var ok: int := if truthAssignment[0] == -1 then 1 else 0; ok + countUnsetVariables(truthAssignment[1..])
  }

  function countTrueLiterals(truthAssignment: seq<int>, clause: seq<int>): int
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    reads this
    ensures 0 <= countTrueLiterals(truthAssignment, clause) <= |clause|
    decreases {this}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      var ok: int := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0; ok + countTrueLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction truthAssignment, clause}*/ prop_countTrueLiterals_initialTruthAssignment(truthAssignment: seq<int>, clause: seq<int>)
    requires validVariablesCount()
    requires validStack()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countTrueLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction truthAssignment, clause}*/ countTrueLiterals0_noLiteralsTrue(truthAssignment: seq<int>, clause: seq<int>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) == 0
    ensures forall literal: int :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction truthAssignment, clause}*/ countTrueLiteralsX_existsTrueLiteral(truthAssignment: seq<int>, clause: seq<int>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) > 0
    ensures exists literal: int :: literal in clause && getLiteralValue(truthAssignment, literal) == 1
    decreases truthAssignment, clause
  {
  }

  predicate validFalseLiteralsCount(truthAssignment: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads this, falseLiteralsCount
    decreases {this, falseLiteralsCount}, truthAssignment
  {
    falseLiteralsCount.Length == |clauses| &&
    forall i: int :: 
      0 <= i < |clauses| ==>
        0 <= falseLiteralsCount[i] == countFalseLiterals(truthAssignment, clauses[i])
  }

  function countFalseLiterals(truthAssignment: seq<int>, clause: seq<int>): int
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    reads this
    ensures 0 <= countFalseLiterals(truthAssignment, clause) <= |clause|
    decreases {this}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      var ok: int := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0; ok + countFalseLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction truthAssignment, clause}*/ prop_countFalseLiterals_initialTruthAssignment(truthAssignment: seq<int>, clause: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countFalseLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
  }

  predicate validLiteralsCount()
    requires validVariablesCount()
    requires validClauses()
    reads this, literalsCount
    decreases {this, literalsCount}
  {
    literalsCount.Length == |clauses| &&
    forall i: int :: 
      0 <= i < |clauses| ==>
        literalsCount[i] == |clauses[i]|
  }

  predicate validPositiveLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, positiveLiteralsToClauses
    decreases {this, positiveLiteralsToClauses}
  {
    positiveLiteralsToClauses.Length == variablesCount &&
    forall variable: int :: 
      0 <= variable < positiveLiteralsToClauses.Length ==>
        validPositiveLiteralToClause(variable, positiveLiteralsToClauses[variable])
  }

  predicate validPositiveLiteralToClause(variable: int, s: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this
    decreases {this}, variable, s
  {
    SeqPredicates.valuesBoundedBy(s, 0, |clauses|) &&
    SeqPredicates.orderedAsc(s) &&
    (forall clauseIndex: int :: 
      clauseIndex in s ==>
        variable + 1 in clauses[clauseIndex]) &&
    forall clauseIndex: int :: 
      0 <= clauseIndex < |clauses| &&
      clauseIndex !in s ==>
        variable + 1 !in clauses[clauseIndex]
  }

  predicate validNegativeLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, negativeLiteralsToClauses
    decreases {this, negativeLiteralsToClauses}
  {
    negativeLiteralsToClauses.Length == variablesCount &&
    forall v: int :: 
      0 <= v < negativeLiteralsToClauses.Length ==>
        validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
  }

  predicate validNegativeLiteralsToClause(variable: int, s: seq<int>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this
    decreases {this}, variable, s
  {
    SeqPredicates.valuesBoundedBy(s, 0, |clauses|) &&
    SeqPredicates.orderedAsc(s) &&
    (forall clauseIndex: int :: 
      clauseIndex in s ==>
        -variable - 1 in clauses[clauseIndex]) &&
    forall clauseIndex: int :: 
      0 <= clauseIndex < |clauses| &&
      clauseIndex !in s ==>
        -variable - 1 !in clauses[clauseIndex]
  }

  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    truthAssignment != trueLiteralsCount &&
    truthAssignment != falseLiteralsCount &&
    truthAssignment != literalsCount &&
    trueLiteralsCount != falseLiteralsCount &&
    trueLiteralsCount != literalsCount &&
    falseLiteralsCount != literalsCount &&
    positiveLiteralsToClauses != negativeLiteralsToClauses
  }

  predicate valid()
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, stack, stack.stack, truthAssignment, trueLiteralsCount, falseLiteralsCount, literalsCount, satisfiedClauses, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    validReferences() &&
    validVariablesCount() &&
    validClauses() &&
    validStack() &&
    validTruthAssignment() &&
    validSatisfiedClauses(truthAssignment[..]) &&
    validTrueLiteralsCount(truthAssignment[..]) &&
    validFalseLiteralsCount(truthAssignment[..]) &&
    validLiteralsCount() &&
    validPositiveLiteralsToClauses() &&
    validNegativeLiteralsToClauses()
  }

  lemma /*{:_induction oldTau, newTau}*/ clausesNotImpacted_TFArraysSame(oldTau: seq<int>, newTau: seq<int>, variable: int, impactedClauses: seq<int>, impactedClauses': seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires newTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires newTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures forall clauseIndex: int :: 0 <= clauseIndex < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: int :: 0 <= clauseIndex < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
  }

  lemma /*{:_induction oldTau, newTau, clause}*/ setVariable_countTrueLiteralsIncreasesWithOne(oldTau: seq<int>, newTau: seq<int>, variable: int, clause: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> variable + 1 in clause
    requires newTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction oldTau, newTau, clause}*/ setVariable_countFalseLiteralsIncreasesWithOne(oldTau: seq<int>, newTau: seq<int>, variable: int, clause: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> -variable - 1 in clause
    requires newTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction oldTau, newTau, clause}*/ unsetVariable_countTrueLiteralsDecreasesWithOne(oldTau: seq<int>, newTau: seq<int>, variable: int, clause: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> variable + 1 in clause
    requires oldTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction oldTau, newTau, clause}*/ unsetVariable_countFalseLiteralsDecreasesWithOne(oldTau: seq<int>, newTau: seq<int>, variable: int, clause: seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> -variable - 1 in clause
    requires oldTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction oldTau, newTau}*/ undoImpactedClauses_TFSArraysModified(oldTau: seq<int>, newTau: seq<int>, variable: int, impactedClauses: seq<int>, impactedClauses': seq<int>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires oldTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires oldTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: int :: 0 <= x < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == trueLiteralsCount[clauseIndex]
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == falseLiteralsCount[clauseIndex]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures forall clauseIndex: int :: 0 <= clauseIndex < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: int :: 0 <= clauseIndex < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
  }

  lemma notDone_literalsToSet(i: int)
    requires valid()
    requires 0 <= i < |clauses|
    requires falseLiteralsCount[i] < literalsCount[i]
    requires trueLiteralsCount[i] == 0
    requires validClause(clauses[i])
    requires forall literal: int :: literal in clauses[i] ==> validLiteral(literal)
    ensures exists literal: int :: literal in clauses[i] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases i
  {
  }

  lemma /*{:_induction oldTau, newTau}*/ setVariable_unsetVariablesDecreasesWithOne(oldTau: seq<int>, newTau: seq<int>, variable: int)
    requires validVariablesCount()
    requires validVariable(variable)
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires |oldTau| == |newTau|
    requires forall i: int :: 0 <= i < |oldTau| && i != variable ==> oldTau[i] == newTau[i]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures countUnsetVariables(newTau) + 1 == countUnsetVariables(oldTau)
    decreases oldTau, newTau, variable
  {
  }

  predicate isVariableSet(truthAssignment: seq<int>, variable: int)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validVariable(variable)
    reads this
    decreases {this}, truthAssignment, variable
  {
    truthAssignment[variable] != -1
  }
}

module Utils {
  method newInitializedSeq(n: int, d: int) returns (r: array<int>)
    requires 0 < n
    ensures r.Length == n
    ensures forall j: int :: 0 <= j < r.Length ==> r[j] == d
    ensures fresh(r)
    decreases n, d
  {
    r := new int[n];
    var index: int := 0;
    while index < n
      invariant 0 <= index <= r.Length == n
      invariant forall j: int :: 0 <= j < index ==> r[j] == d
      decreases n - index
    {
      r[index] := d;
      index := index + 1;
    }
  }

  function method abs(literal: int): int
    decreases literal
  {
    if literal < 0 then
      -literal
    else
      literal
  }

  function method properClause(clause: seq<int>): bool
    decreases clause
  {
    forall literal: int :: 
      literal in clause ==>
        literal != 0
  }

  function method properClauses(clauses: seq<seq<int>>): bool
    decreases clauses
  {
    |clauses| > 0 &&
    forall clause: seq<int> :: 
      clause in clauses ==>
        properClause(clause)
  }

  lemma prop_seq_predicate(q: int, abc: seq<int>)
    requires forall j: int :: j in abc ==> 0 <= j < q
    ensures forall j: int :: 0 <= j < |abc| ==> 0 <= abc[j] < q
    decreases q, abc
  {
  }
}

module SeqPredicates {
  predicate valueBoundedBy(value: int, min: int, max: int)
    decreases value, min, max
  {
    min <= value < max
  }

  predicate valuesBoundedBy(s: seq<int>, min: int, max: int)
    decreases s, min, max
  {
    (forall el: int :: 
      el in s ==>
        valueBoundedBy(el, min, max)) &&
    forall i: int :: 
      0 <= i < |s| ==>
        valueBoundedBy(s[i], min, max)
  }

  predicate orderedAsc(s: seq<int>)
    decreases s
  {
    forall x: int, y: int :: 
      0 <= x < y < |s| ==>
        s[x] < s[y]
  }
}

class Stack {
  var size: int
  var stack: array<seq<(int, bool)>>
  var variablesCount: int
  ghost var contents: set<(int, bool)>

  constructor (varCount: int)
    requires varCount > 0
    ensures valid()
    ensures this.variablesCount == varCount
    ensures this.contents == {}
    ensures forall x: int :: 0 <= x < stack.Length ==> |stack[x]| == 0
    ensures fresh(stack)
    decreases varCount
  {
    this.size := 0;
    this.variablesCount := varCount;
    this.stack := new seq<(int, bool)>[varCount];
    this.contents := {};
    new;
    var i := 0;
    while i < stack.Length
      invariant 0 <= i <= stack.Length
      invariant forall j: int :: 0 <= j < i ==> stack[j] == []
      decreases stack.Length - i
      modifies stack
    {
      stack[i] := [];
      i := i + 1;
    }
  }

  predicate validVariablesCount()
    reads this
    decreases {this}
  {
    variablesCount > 0
  }

  predicate validVariable(variable: int)
    requires validVariablesCount()
    reads this
    decreases {this}, variable
  {
    0 <= variable < variablesCount
  }

  predicate valid()
    reads this, stack
    decreases {this, stack}
  {
    validVariablesCount() &&
    stack.Length == variablesCount &&
    0 <= size <= stack.Length &&
    (forall i: int :: 
      0 <= i < size - 1 ==>
        |stack[i]| > 0) &&
    (forall i: int :: 
      size <= i < stack.Length ==>
        stack[i] == []) &&
    (forall i: int :: 
      0 <= i < stack.Length ==>
        forall j: int :: 
          0 <= j < |stack[i]| ==>
            validVariable(stack[i][j].0)) &&
    (forall i: int :: 
      0 <= i < stack.Length ==>
        forall j: int :: 
          0 <= j < |stack[i]| ==>
            (forall i': int :: 
              0 <= i' < stack.Length &&
              i != i' ==>
                forall j': int :: 
                  0 <= j' < |stack[i']| ==>
                    stack[i][j].0 != stack[i'][j'].0) &&
            forall j': int :: 
              0 <= j' < |stack[i]| &&
              j != j' ==>
                stack[i][j].0 != stack[i][j'].0) &&
    (forall i: int :: 
      0 <= i < stack.Length ==>
        forall j: int :: 
          0 <= j < |stack[i]| ==>
            stack[i][j] in contents) &&
    forall c: (int, bool) :: 
      c in contents ==>
        exists i: int, j: int :: 
          0 <= i < stack.Length &&
          0 <= j < |stack[i]| &&
          stack[i][j] == c
  }

  function getLastLayer(): set<(int, bool)>
    requires 0 < size <= stack.Length
    reads this, stack
    decreases {this, stack}
  {
    set x: (int, bool) {:trigger identity(x)} | x in stack[size - 1] && identity(x)
  }

  lemma variableNotInContents_variableNotInStack(variable: int)
    requires valid()
    requires (variable, false) !in contents && (variable, true) !in contents
    ensures forall i: int, j: int :: 0 <= i < stack.Length && 0 <= j < |stack[i]| ==> stack[i][j].0 != variable
    decreases variable
  {
  }

  predicate occursInStack(variable: int)
    requires valid()
    requires validVariable(variable)
    requires size > 0
    requires size == stack.Length
    requires |stack[size - 1]| > 0
    reads this, stack
    decreases {this, stack}, variable
  {
    exists j: int :: 
      0 <= j < size &&
      stack[j][0].0 == variable
  }

  predicate occursInContents(variable: int)
    requires valid()
    requires validVariable(variable)
    requires size > 0
    requires size == stack.Length
    requires |stack[size - 1]| > 0
    reads this, stack
    decreases {this, stack}, variable
  {
    exists x: (int, bool) :: 
      x in contents &&
      x.0 == variable
  }

  lemma ifFull_containsAllVariables()
    requires valid()
    requires size > 0
    requires size == stack.Length
    requires |stack[size - 1]| > 0
    ensures forall v: int :: 0 <= v < size ==> occursInStack(v)
    ensures forall v: int :: 0 <= v < size ==> occursInContents(v)
  {
  }

  method createNewLayer()
    requires valid()
    requires size < stack.Length
    requires size > 0 ==> |stack[size - 1]| > 0
    modifies this
    ensures valid()
    ensures variablesCount == old(variablesCount)
    ensures contents == old(contents)
    ensures stack == old(stack)
    ensures size == old(size) + 1
    ensures stack[size - 1] == []
  {
    size := size + 1;
    assert forall i: int :: 0 <= i < stack.Length ==> stack[i] == old(stack[i]);
  }
}
")]

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Count {
      get { return this.setImpl.Count; }
    }
    public long LongCount {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Count < other.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      } else if (t is T && dict.ContainsKey((T)(object)t)) {
        return dict[(T)(object)t];
      } else {
        return BigInteger.Zero;
      }
    }
    public MultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = dict;
#endif
        return new MultiSet<T>(r, i);
      } else {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = new Dictionary<T, int>(dict);
#endif
        r[(T)(object)t] = (int)i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (int i = 0; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Count {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public Set<U> Keys {
      get {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values {
      get {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<_System.Tuple2<U, V>> Items {
      get {
        HashSet<_System.Tuple2<U, V>> result = new HashSet<_System.Tuple2<U, V>>();
        if (hasNullValue) {
          result.Add(_System.Tuple2<U, V>.create(default(U), nullValue));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(_System.Tuple2<U, V>.create(kvp.Key, kvp.Value));
        }
        return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Count {
      get { return elmts.Length; }
    }
    public long LongCount {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }
    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    // Computing forall/exists quantifiers
    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@Tuple2<T0,T1>;
      return oth != null && Dafny.Helpers.AreEqual(this._0, oth._0) && Dafny.Helpers.AreEqual(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    static Tuple2<T0,T1> theDefault;
    public static Tuple2<T0,T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@Tuple2<T0,T1>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>());
        }
        return theDefault;
      }
    }
    public static Tuple2<T0,T1> _DafnyDefaultValue() { return Default; }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake3 { get { return true; } }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++)
        a[i0] = z;
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
  }








  public class Tuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    static Tuple0 theDefault;
    public static Tuple0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple0();
        }
        return theDefault;
      }
    }
    public static Tuple0 _DafnyDefaultValue() { return Default; }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public bool is____hMake0 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace _0_MyDatatypes_Compile {

  public abstract class Maybe<T> {
    public Maybe() { }
    static Maybe<T> theDefault;
    public static Maybe<T> Default {
      get {
        if (theDefault == null) {
          theDefault = new _0_MyDatatypes_Compile.Maybe_Error<T>(Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static Maybe<T> _DafnyDefaultValue() { return Default; }
    public static Maybe<T> create_Error(Dafny.Sequence<char> _a0) {
      return new Maybe_Error<T>(_a0);
    }
    public static Maybe<T> create_Just(T @value) {
      return new Maybe_Just<T>(@value);
    }
    public bool is_Error { get { return this is Maybe_Error<T>; } }
    public bool is_Just { get { return this is Maybe_Just<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Maybe_Just<T>)d).@value; 
      }
    }
  }
  public class Maybe_Error<T> : Maybe<T> {
    public readonly Dafny.Sequence<char> _a0;
    public Maybe_Error(Dafny.Sequence<char> _a0) {
      this._a0 = _a0;
    }
    public override bool Equals(object other) {
      var oth = other as _0_MyDatatypes_Compile.Maybe_Error<T>;
      return oth != null && Dafny.Helpers.AreEqual(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "_0_MyDatatypes_Compile.Maybe.Error";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Maybe_Just<T> : Maybe<T> {
    public readonly T @value;
    public Maybe_Just(T @value) {
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as _0_MyDatatypes_Compile.Maybe_Just<T>;
      return oth != null && Dafny.Helpers.AreEqual(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "_0_MyDatatypes_Compile.Maybe.Just";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

} // end of namespace _0_MyDatatypes_Compile
namespace _2_Parser_Compile {


  public partial class __default {
    public static Dafny.Sequence<char> skipLine(Dafny.Sequence<char> content) {
      if ((new BigInteger((content).Count)) == (new BigInteger(0))) {
        return content;
      } else  {
        if (((content).Select(new BigInteger(0))) == ('\n')) {
          return (content).Drop(new BigInteger(1));
        } else  {
          return _2_Parser_Compile.__default.skipLine((content).Drop(new BigInteger(1)));
        }
      }
    }
    public static Dafny.Sequence<char> skipWhiteSpaces(Dafny.Sequence<char> content) {
      if ((new BigInteger((content).Count)) == (new BigInteger(0))) {
        return content;
      } else  {
        if (((content).Select(new BigInteger(0))) == (' ')) {
          return _2_Parser_Compile.__default.skipWhiteSpaces((content).Drop(new BigInteger(1)));
        } else  {
          if (((content).Select(new BigInteger(0))) == ('\n')) {
            return _2_Parser_Compile.__default.skipWhiteSpaces((content).Drop(new BigInteger(1)));
          } else  {
            return content;
          }
        }
      }
    }
    public static bool isDigit(char chr) {
      return (('0') <= (chr)) && ((chr) <= ('9'));
    }
    public static BigInteger toInt(char chr) {
      return (new BigInteger(chr)) - (new BigInteger('0'));
    }
    public static _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> extractDigits(Dafny.Sequence<char> content) {
      if ((new BigInteger((content).Count)) == (new BigInteger(0))) {
        return @_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>.create(Dafny.Sequence<BigInteger>.FromElements(), content);
      } else  {
        if (_2_Parser_Compile.__default.isDigit((content).Select(new BigInteger(0)))) {
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> _let_tmp_rhs0 = _2_Parser_Compile.__default.extractDigits((content).Drop(new BigInteger(1)));
          Dafny.Sequence<BigInteger> _371_h = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs0)._0;
          Dafny.Sequence<char> _372_tail = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs0)._1;
          return @_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>.create((Dafny.Sequence<BigInteger>.FromElements(_2_Parser_Compile.__default.toInt((content).Select(new BigInteger(0))))).Concat(_371_h), _372_tail);
        } else  {
          return @_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>.create(Dafny.Sequence<BigInteger>.FromElements(), content);
        }
      }
    }
    public static BigInteger joinInts(BigInteger number, Dafny.Sequence<BigInteger> ints)
    {
      if ((new BigInteger((ints).Count)) == (new BigInteger(0))) {
        return number;
      } else  {
        return _2_Parser_Compile.__default.joinInts(((number) * (new BigInteger(10))) + ((ints).Select(new BigInteger(0))), (ints).Drop(new BigInteger(1)));
      }
    }
    public static _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>> getNextNumber(Dafny.Sequence<char> content) {
      if ((new BigInteger((content).Count)) == (new BigInteger(0))) {
        return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>.create_Error(Dafny.Sequence<char>.FromString("content finished unexpectatly"));
      } else  {
        if (((content).Select(new BigInteger(0))) == ('-')) {
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> _let_tmp_rhs1 = _2_Parser_Compile.__default.extractDigits((content).Drop(new BigInteger(1)));
          Dafny.Sequence<BigInteger> _373_digits = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs1)._0;
          Dafny.Sequence<char> _374_newContent = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs1)._1;
          if ((new BigInteger((_373_digits).Count)) == (new BigInteger(0))) {
            return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>.create_Error(Dafny.Sequence<char>.FromString("only alpha characters ahead, no numbers after -"));
          } else  {
            BigInteger _375_number = _2_Parser_Compile.__default.joinInts(new BigInteger(0), _373_digits);
            return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>.create_Just(@_System.Tuple2<BigInteger,Dafny.Sequence<char>>.create((new BigInteger(0)) - (_375_number), _374_newContent));
          }
        } else  {
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> _let_tmp_rhs2 = _2_Parser_Compile.__default.extractDigits(content);
          Dafny.Sequence<BigInteger> _376_digits = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs2)._0;
          Dafny.Sequence<char> _377_newContent = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs2)._1;
          if ((new BigInteger((_376_digits).Count)) == (new BigInteger(0))) {
            return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>.create_Error(Dafny.Sequence<char>.FromString("only alpha characters ahead, no numbers"));
          } else  {
            BigInteger _378_number = _2_Parser_Compile.__default.joinInts(new BigInteger(0), _376_digits);
            return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>.create_Just(@_System.Tuple2<BigInteger,Dafny.Sequence<char>>.create(_378_number, _377_newContent));
          }
        }
      }
    }
    public static _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> extractNumbers(Dafny.Sequence<char> content) {
      Dafny.Sequence<char> _379_content_k = _2_Parser_Compile.__default.skipWhiteSpaces(content);
      _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>> _source0 = _2_Parser_Compile.__default.getNextNumber(_379_content_k);
      if (_source0.is_Error) {
        Dafny.Sequence<char> _380___v0 = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source0)._a0;
        return @_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>.create(Dafny.Sequence<BigInteger>.FromElements(), _379_content_k);
      } else  {
        _System.Tuple2<BigInteger,Dafny.Sequence<char>> _381___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source0).@value;
        _System.Tuple2<BigInteger,Dafny.Sequence<char>> _source1 = _381___ms_h0;
 {
          BigInteger _382_number = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source1)._0;
          Dafny.Sequence<char> _383_content_k_k = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source1)._1;
          Dafny.Sequence<char> _384_content_k_k_k = _2_Parser_Compile.__default.skipWhiteSpaces(_383_content_k_k);
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> _let_tmp_rhs3 = _2_Parser_Compile.__default.extractNumbers(_384_content_k_k_k);
          Dafny.Sequence<BigInteger> _385_fst = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs3)._0;
          Dafny.Sequence<char> _386_snd = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs3)._1;
          return @_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>.create((Dafny.Sequence<BigInteger>.FromElements(_382_number)).Concat(_385_fst), _386_snd);
        }
      }
    }
    public static _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>> getNextClause(Dafny.Sequence<BigInteger> numbers) {
      if ((new BigInteger((numbers).Count)) == (new BigInteger(0))) {
        return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>.create_Error(Dafny.Sequence<char>.FromString("no 0 there"));
      } else  {
        if (((numbers).Select(new BigInteger(0))) == (new BigInteger(0))) {
          return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>.create_Just(@_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>.create(Dafny.Sequence<BigInteger>.FromElements(), (numbers).Drop(new BigInteger(1))));
        } else  {
          Dafny.Sequence<BigInteger> _387_head = Dafny.Sequence<BigInteger>.FromElements((numbers).Select(new BigInteger(0)));
          _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>> _source2 = _2_Parser_Compile.__default.getNextClause((numbers).Drop(new BigInteger(1)));
          if (_source2.is_Error) {
            Dafny.Sequence<char> _388_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>)_source2)._a0;
            return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>.create_Error(_388_m);
          } else  {
            _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>> _389___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>)_source2).@value;
            _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>> _source3 = _389___ms_h0;
 {
              Dafny.Sequence<BigInteger> _390_tail = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>)_source3)._0;
              Dafny.Sequence<BigInteger> _391_numbers = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>)_source3)._1;
              return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>.create_Just(@_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>.create((_387_head).Concat(_390_tail), _391_numbers));
            }
          }
        }
      }
    }
    public static _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>> getClauses(BigInteger clausesCount, Dafny.Sequence<BigInteger> numbers)
    {
      if (((clausesCount) <= (new BigInteger(0))) || ((new BigInteger((numbers).Count)) == (new BigInteger(0)))) {
        return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>.create_Just(@_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>.create(Dafny.Sequence<Dafny.Sequence<BigInteger>>.FromElements(), numbers));
      } else  {
        _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>> _source4 = _2_Parser_Compile.__default.getNextClause(numbers);
        if (_source4.is_Error) {
          Dafny.Sequence<char> _392_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>)_source4)._a0;
          return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>.create_Error(_392_m);
        } else  {
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>> _393___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>>)_source4).@value;
          _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>> _source5 = _393___ms_h0;
 {
            Dafny.Sequence<BigInteger> _394_clause = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>)_source5)._0;
            Dafny.Sequence<BigInteger> _395_numbers = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<BigInteger>>)_source5)._1;
            _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>> _source6 = _2_Parser_Compile.__default.getClauses((clausesCount) - (new BigInteger(1)), _395_numbers);
            if (_source6.is_Error) {
              Dafny.Sequence<char> _396_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>)_source6)._a0;
              return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>.create_Error(_396_m);
            } else  {
              _System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>> _397___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>)_source6).@value;
              _System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>> _source7 = _397___ms_h0;
 {
                Dafny.Sequence<Dafny.Sequence<BigInteger>> _398_clauses = ((_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>)_source7)._0;
                Dafny.Sequence<BigInteger> _399_numbers = ((_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>)_source7)._1;
                return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>.create_Just(@_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>.create((Dafny.Sequence<Dafny.Sequence<BigInteger>>.FromElements(_394_clause)).Concat(_398_clauses), _399_numbers));
              }
            }
          }
        }
      }
    }
    public static _0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>> getToInput(Dafny.Sequence<char> content) {
      Dafny.Sequence<char> _400_content = _2_Parser_Compile.__default.skipWhiteSpaces(content);
      if ((new BigInteger((_400_content).Count)) == (new BigInteger(0))) {
        return @_0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>>.create_Error(Dafny.Sequence<char>.FromString("nothing found"));
      } else  {
        if (((_400_content).Select(new BigInteger(0))) == ('c')) {
          return _2_Parser_Compile.__default.getToInput(_2_Parser_Compile.__default.skipLine(_400_content));
        } else  {
          if (((_400_content).Select(new BigInteger(0))) == ('p')) {
            Dafny.Sequence<char> _401_content = _2_Parser_Compile.__default.skipWhiteSpaces((_400_content).Drop(new BigInteger(1)));
            if ((new BigInteger((_401_content).Count)) < (new BigInteger(3))) {
              return @_0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>>.create_Error(Dafny.Sequence<char>.FromString("input not correctly formated"));
            } else  {
              return @_0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>>.create_Just(_2_Parser_Compile.__default.skipWhiteSpaces((_401_content).Drop(new BigInteger(3))));
            }
          } else  {
            return @_0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>>.create_Error(Dafny.Sequence<char>.FromString("invalid symbol"));
          }
        }
      }
    }
    public static _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>> parseContent(Dafny.Sequence<char> content) {
      _0_MyDatatypes_Compile.Maybe<Dafny.Sequence<char>> _source8 = _2_Parser_Compile.__default.getToInput(content);
      if (_source8.is_Error) {
        Dafny.Sequence<char> _402_m = ((_0_MyDatatypes_Compile.Maybe_Error<Dafny.Sequence<char>>)_source8)._a0;
        return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>.create_Error(_402_m);
      } else  {
        Dafny.Sequence<char> _403_content = ((_0_MyDatatypes_Compile.Maybe_Just<Dafny.Sequence<char>>)_source8).@value;
        _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>> _source9 = _2_Parser_Compile.__default.getNextNumber(_403_content);
        if (_source9.is_Error) {
          Dafny.Sequence<char> _404_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source9)._a0;
          return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>.create_Error(_404_m);
        } else  {
          _System.Tuple2<BigInteger,Dafny.Sequence<char>> _405___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source9).@value;
          _System.Tuple2<BigInteger,Dafny.Sequence<char>> _source10 = _405___ms_h0;
 {
            BigInteger _406_variablesCount = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source10)._0;
            Dafny.Sequence<char> _407_content = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source10)._1;
            _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<char>>> _source11 = _2_Parser_Compile.__default.getNextNumber(_2_Parser_Compile.__default.skipWhiteSpaces(_407_content));
            if (_source11.is_Error) {
              Dafny.Sequence<char> _408_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source11)._a0;
              return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>.create_Error(_408_m);
            } else  {
              _System.Tuple2<BigInteger,Dafny.Sequence<char>> _409___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<BigInteger,Dafny.Sequence<char>>>)_source11).@value;
              _System.Tuple2<BigInteger,Dafny.Sequence<char>> _source12 = _409___ms_h0;
 {
                BigInteger _410_clausesCount = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source12)._0;
                Dafny.Sequence<char> _411_content = ((_System.Tuple2<BigInteger,Dafny.Sequence<char>>)_source12)._1;
                _System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>> _let_tmp_rhs4 = _2_Parser_Compile.__default.extractNumbers(_411_content);
                Dafny.Sequence<BigInteger> _412_numbers = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs4)._0;
                Dafny.Sequence<char> _413___v1 = ((_System.Tuple2<Dafny.Sequence<BigInteger>,Dafny.Sequence<char>>)_let_tmp_rhs4)._1;
                _0_MyDatatypes_Compile.Maybe<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>> _source13 = _2_Parser_Compile.__default.getClauses(_410_clausesCount, _412_numbers);
                if (_source13.is_Error) {
                  Dafny.Sequence<char> _414_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>)_source13)._a0;
                  return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>.create_Error(_414_m);
                } else  {
                  _System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>> _415___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>>)_source13).@value;
                  _System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>> _source14 = _415___ms_h0;
 {
                    Dafny.Sequence<Dafny.Sequence<BigInteger>> _416_clauses = ((_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>)_source14)._0;
                    Dafny.Sequence<BigInteger> _417_content = ((_System.Tuple2<Dafny.Sequence<Dafny.Sequence<BigInteger>>,Dafny.Sequence<BigInteger>>)_source14)._1;
                    return @_0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>.create_Just(@_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>.create(_406_variablesCount, _416_clauses));
                  }
                }
              }
            }
          }
        }
      }
    }
  }
} // end of namespace _2_Parser_Compile
namespace FileInput {

  public partial class Reader {
  }

} // end of namespace FileInput
namespace _7_Input_Compile {




  public partial class __default {
    public static _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>> getInput() {
      return _2_Parser_Compile.__default.parseContent(Dafny.Helpers.SeqFromArray(FileInput.Reader.getContent()).Drop(new BigInteger(0)));
    }
    public static BigInteger getTimestamp() {
      return FileInput.Reader.getTimestamp();
    }
  }
} // end of namespace _7_Input_Compile
namespace _8_Utils_Compile {

  public partial class __default {
    public static void newInitializedSeq(BigInteger n, BigInteger d, out BigInteger[] r)
    {
    TAIL_CALL_START: ;
      r = new BigInteger[0];
      var _nw0 = new BigInteger[(int)(n)];
      r = _nw0;
      BigInteger _418_index;
      _418_index = new BigInteger(0);
      while ((_418_index) < (n)) {
        (r)[(int)((_418_index))] = d;
        _418_index = (_418_index) + (new BigInteger(1));
      }
    }
    public static BigInteger abs(BigInteger literal) {
      if ((literal) < (new BigInteger(0))) {
        return (new BigInteger(0)) - (literal);
      } else  {
        return literal;
      }
    }
    public static bool properClause(Dafny.Sequence<BigInteger> clause) {
      return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.SingleValue<BigInteger>(new BigInteger(0)), true, (((_419_literal) => {
        return !((clause).Contains(_419_literal)) || ((_419_literal) != (new BigInteger(0)));
      })));
    }
    public static bool properClauses(Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses) {
      return ((new BigInteger((clauses).Count)) > (new BigInteger(0))) && (Dafny.Helpers.Quantifier<Dafny.Sequence<BigInteger>>((clauses).UniqueElements, true, (((_420_clause) => {
        return !((clauses).Contains(_420_clause)) || (_8_Utils_Compile.__default.properClause(_420_clause));
      }))));
    }
  }
} // end of namespace _8_Utils_Compile
namespace _9_SeqPredicates_Compile {

} // end of namespace _9_SeqPredicates_Compile
namespace _module {

  public partial class __default {
    public static bool checkClauses(BigInteger variablesCount, Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses)
    {
      return Dafny.Helpers.Quantifier<Dafny.Sequence<BigInteger>>((clauses).UniqueElements, true, (((_421_clause) => {
        return !((clauses).Contains(_421_clause)) || (Dafny.Helpers.Quantifier<BigInteger>((_421_clause).UniqueElements, true, (((_422_literal) => {
          return !((_421_clause).Contains(_422_literal)) || ((((_422_literal) < (new BigInteger(0))) && (((new BigInteger(0)) < ((new BigInteger(0)) - (_422_literal))) && (((new BigInteger(0)) - (_422_literal)) <= (variablesCount)))) || (((_422_literal) > (new BigInteger(0))) && (((new BigInteger(0)) < (_422_literal)) && ((_422_literal) <= (variablesCount)))));
        }))));
      })));
    }
    public static bool sortedClauses(Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses) {
      return Dafny.Helpers.Quantifier<Dafny.Sequence<BigInteger>>((clauses).UniqueElements, true, (((_423_clause) => {
        return !((clauses).Contains(_423_clause)) || (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((_423_clause).Count)), true, (((_424_x) => {
          return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_424_x) + (new BigInteger(1)), new BigInteger((_423_clause).Count)), true, (((_425_y) => {
            return !((((new BigInteger(0)) <= (_424_x)) && ((_424_x) < (_425_y))) && ((_425_y) < (new BigInteger((_423_clause).Count)))) || (((_423_clause).Select(_424_x)) < ((_423_clause).Select(_425_y)));
          })));
        }))));
      })));
    }
    public static void sort(BigInteger variablesCount, Dafny.Sequence<BigInteger> clause, out Dafny.Sequence<BigInteger> newClause)
    {
    TAIL_CALL_START: ;
      newClause = Dafny.Sequence<BigInteger>.Empty;
      BigInteger _426_i;
      _426_i = new BigInteger(0);
      newClause = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _427_lastMin;
      _427_lastMin = ((new BigInteger(0)) - (variablesCount)) - (new BigInteger(1));
      while ((_426_i) < (new BigInteger((clause).Count))) {
        BigInteger _428_j;
        _428_j = new BigInteger(0);
        BigInteger _429_min;
        _429_min = (variablesCount) + (new BigInteger(1));
        while ((_428_j) < (new BigInteger((clause).Count))) {
          if (((_427_lastMin) < ((clause).Select(_428_j))) && (((clause).Select(_428_j)) < (_429_min))) {
            _429_min = (clause).Select(_428_j);
          }
          _428_j = (_428_j) + (new BigInteger(1));
        }
        newClause = (newClause).Concat(Dafny.Sequence<BigInteger>.FromElements(_429_min));
        _427_lastMin = _429_min;
        _426_i = (_426_i) + (new BigInteger(1));
      }
    }
    public static void prepare(BigInteger variablesCount, Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses, out Dafny.Sequence<Dafny.Sequence<BigInteger>> newClauses)
    {
    TAIL_CALL_START: ;
      newClauses = Dafny.Sequence<Dafny.Sequence<BigInteger>>.Empty;
      BigInteger _430_k;
      _430_k = new BigInteger(0);
      newClauses = Dafny.Sequence<Dafny.Sequence<BigInteger>>.FromElements();
      while ((_430_k) < (new BigInteger((clauses).Count))) {
        Dafny.Sequence<BigInteger> _431_newClause;
        Dafny.Sequence<BigInteger> _out0;
        __default.sort(variablesCount, (clauses).Select(_430_k), out _out0);
        _431_newClause = _out0;
        newClauses = (newClauses).Concat(Dafny.Sequence<Dafny.Sequence<BigInteger>>.FromElements(_431_newClause));
        _430_k = (_430_k) + (new BigInteger(1));
      }
    }
    public static void Main()
    {
    TAIL_CALL_START: ;
      _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>> _432_input;
      _432_input = _7_Input_Compile.__default.getInput();
      _0_MyDatatypes_Compile.Maybe<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>> _source15 = _432_input;
      if (_source15.is_Error) {
        Dafny.Sequence<char> _433_m = ((_0_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>)_source15)._a0;
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Error: "));
        Dafny.Helpers.Print(_433_m);
      } else  {
        _System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>> _434___ms_h0 = ((_0_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>>)_source15).@value;
        _System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>> _source16 = _434___ms_h0;
 {
          BigInteger _435_variablesCount = ((_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>)_source16)._0;
          Dafny.Sequence<Dafny.Sequence<BigInteger>> _436_clauses = ((_System.Tuple2<BigInteger,Dafny.Sequence<Dafny.Sequence<BigInteger>>>)_source16)._1;
          Dafny.Sequence<Dafny.Sequence<BigInteger>> _437_preparedClauses;
          Dafny.Sequence<Dafny.Sequence<BigInteger>> _out1;
          __default.prepare(_435_variablesCount, _436_clauses, out _out1);
          _437_preparedClauses = _out1;
          if (((_435_variablesCount) > (new BigInteger(0))) && ((new BigInteger((_437_preparedClauses).Count)) > (new BigInteger(0)))) {
            if (__default.checkClauses(_435_variablesCount, _437_preparedClauses)) {
              if (__default.sortedClauses(_437_preparedClauses)) {
                Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Starting ... \n"));
                BigInteger _438_starttime;
                _438_starttime = _7_Input_Compile.__default.getTimestamp();
                Formula _439_formula;
                var _nw1 = new Formula();
                _nw1.__ctor(_435_variablesCount, _437_preparedClauses);
                _439_formula = _nw1;
                SATSolver _440_solver;
                var _nw2 = new SATSolver();
                _nw2.__ctor(_439_formula);
                _440_solver = _nw2;
                SAT__UNSAT _441_solution;
                SAT__UNSAT _out2;
                (_440_solver).solve(out _out2);
                _441_solution = _out2;
                Dafny.BigRational _442_totalTime;
                _442_totalTime = (new Dafny.BigRational(((_7_Input_Compile.__default.getTimestamp()) - (_438_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
                SAT__UNSAT _source17 = _441_solution;
                if (_source17.is_SAT) {
                  Dafny.Sequence<BigInteger> _443_x = ((SAT__UNSAT_SAT)_source17).tau;
                  Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("SAT!"));
                } else  {
                  Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("UNSAT!"));
                }
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Time to solve: "));
                Dafny.Helpers.Print(_442_totalTime);
                Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
              } else {
                Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Literals not in order"));
              }
            } else {
              Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Literals not in [-variablesCount, variablesCount]-{0} interval"));
            }
          }
        }
      }
    }
  }

  public abstract class SAT__UNSAT {
    public SAT__UNSAT() { }
    static SAT__UNSAT theDefault;
    public static SAT__UNSAT Default {
      get {
        if (theDefault == null) {
          theDefault = new SAT__UNSAT_SAT(Dafny.Sequence<BigInteger>.Empty);
        }
        return theDefault;
      }
    }
    public static SAT__UNSAT _DafnyDefaultValue() { return Default; }
    public static SAT__UNSAT create_SAT(Dafny.Sequence<BigInteger> tau) {
      return new SAT__UNSAT_SAT(tau);
    }
    public static SAT__UNSAT create_UNSAT() {
      return new SAT__UNSAT_UNSAT();
    }
    public bool is_SAT { get { return this is SAT__UNSAT_SAT; } }
    public bool is_UNSAT { get { return this is SAT__UNSAT_UNSAT; } }
    public Dafny.Sequence<BigInteger> dtor_tau {
      get {
        var d = this;
        return ((SAT__UNSAT_SAT)d).tau; 
      }
    }
  }
  public class SAT__UNSAT_SAT : SAT__UNSAT {
    public readonly Dafny.Sequence<BigInteger> tau;
    public SAT__UNSAT_SAT(Dafny.Sequence<BigInteger> tau) {
      this.tau = tau;
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_SAT;
      return oth != null && Dafny.Helpers.AreEqual(this.tau, oth.tau);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tau));
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.SAT";
      s += "(";
      s += Dafny.Helpers.ToString(this.tau);
      s += ")";
      return s;
    }
  }
  public class SAT__UNSAT_UNSAT : SAT__UNSAT {
    public SAT__UNSAT_UNSAT() {
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_UNSAT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.UNSAT";
      return s;
    }
  }

  public partial class SATSolver {
    public Formula formula = default(Formula);
    public void __ctor(Formula f_k)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).formula = f_k;
    }
    public void step(BigInteger literal, bool @value, out SAT__UNSAT result)
    {
      result = SAT__UNSAT.Default;
      (this.formula).newLayerOnStack();
      (this.formula).setLiteral(literal, @value);
      { }
      SAT__UNSAT _out3;
      (this).solve(out _out3);
      result = _out3;
      (this.formula).undoLayerOnStack();
      { }
      { }
      result = result;
      return;
    }
    public void solve(out SAT__UNSAT result)
    {
      result = SAT__UNSAT.Default;
      if ((this.formula).hasEmptyClause()) {
        { }
        result = @SAT__UNSAT.create_UNSAT();
        return;
      }
      if ((this.formula).isEmpty()) {
        { }
        result = @SAT__UNSAT.create_SAT(Dafny.Helpers.SeqFromArray(this.formula.truthAssignment));
        { }
        result = result;
        return;
      }
      { }
      BigInteger _444_literal;
      BigInteger _out4;
      (this.formula).chooseLiteral(out _out4);
      _444_literal = _out4;
      SAT__UNSAT _out5;
      (this).step(_444_literal, true, out _out5);
      result = _out5;
      if ((result).is_SAT) {
        result = result;
        return;
      }
      SAT__UNSAT _out6;
      (this).step(_444_literal, false, out _out6);
      result = _out6;
      if ((result).is_UNSAT) {
        { }
        { }
      }
      result = result;
      return;
    }
  }



  public partial class Formula : DataStructures {
    public BigInteger _variablesCount = BigInteger.Zero;
    public BigInteger variablesCount {
      get {
        return this._variablesCount;
      }
      set {
        this._variablesCount = value;
      }
    }
    public Dafny.Sequence<Dafny.Sequence<BigInteger>> _clauses = Dafny.Sequence<Dafny.Sequence<BigInteger>>.Empty;
    public Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses {
      get {
        return this._clauses;
      }
      set {
        this._clauses = value;
      }
    }
    public Stack _stack = default(Stack);
    public Stack stack {
      get {
        return this._stack;
      }
      set {
        this._stack = value;
      }
    }
    public BigInteger[] _truthAssignment = new BigInteger[0];
    public BigInteger[] truthAssignment {
      get {
        return this._truthAssignment;
      }
      set {
        this._truthAssignment = value;
      }
    }
    public bool[] _satisfiedClauses = new bool[0];
    public bool[] satisfiedClauses {
      get {
        return this._satisfiedClauses;
      }
      set {
        this._satisfiedClauses = value;
      }
    }
    public BigInteger[] _trueLiteralsCount = new BigInteger[0];
    public BigInteger[] trueLiteralsCount {
      get {
        return this._trueLiteralsCount;
      }
      set {
        this._trueLiteralsCount = value;
      }
    }
    public BigInteger[] _falseLiteralsCount = new BigInteger[0];
    public BigInteger[] falseLiteralsCount {
      get {
        return this._falseLiteralsCount;
      }
      set {
        this._falseLiteralsCount = value;
      }
    }
    public BigInteger[] _literalsCount = new BigInteger[0];
    public BigInteger[] literalsCount {
      get {
        return this._literalsCount;
      }
      set {
        this._literalsCount = value;
      }
    }
    public Dafny.Sequence<BigInteger>[] _positiveLiteralsToClauses = new Dafny.Sequence<BigInteger>[0];
    public Dafny.Sequence<BigInteger>[] positiveLiteralsToClauses {
      get {
        return this._positiveLiteralsToClauses;
      }
      set {
        this._positiveLiteralsToClauses = value;
      }
    }
    public Dafny.Sequence<BigInteger>[] _negativeLiteralsToClauses = new Dafny.Sequence<BigInteger>[0];
    public Dafny.Sequence<BigInteger>[] negativeLiteralsToClauses {
      get {
        return this._negativeLiteralsToClauses;
      }
      set {
        this._negativeLiteralsToClauses = value;
      }
    }
    public _System.Tuple2<BigInteger,BigInteger> convertLVtoVI(BigInteger literal, bool @value)
    {
      BigInteger _445_variable = (this).getVariableFromLiteral(literal);
      BigInteger _446_v = (@value) ? (new BigInteger(1)) : (new BigInteger(0));
      BigInteger _447_val = ((literal) < (new BigInteger(0))) ? ((new BigInteger(1)) - (_446_v)) : (_446_v);
      return @_System.Tuple2<BigInteger,BigInteger>.create(_445_variable, _447_val);
    }
    public BigInteger getVariableFromLiteral(BigInteger literal) {
      return (_8_Utils_Compile.__default.abs(literal)) - (new BigInteger(1));
    }
    public void __ctor(BigInteger variablesCount, Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses)
    {
      (this).variablesCount = variablesCount;
      (this).clauses = clauses;
      var _nw3 = new Stack();
      _nw3.__ctor(variablesCount);
      (this).stack = _nw3;
      { }
      { }
      { }
      { }
      { }
      BigInteger[] _out7;
      _8_Utils_Compile.__default.newInitializedSeq(variablesCount, (new BigInteger(0)) - (new BigInteger(1)), out _out7);
      (this).truthAssignment = _out7;
      { }
      var _nw4 = new BigInteger[(int)(new BigInteger((this.clauses).Count))];
      (this).trueLiteralsCount = _nw4;
      var _nw5 = new BigInteger[(int)(new BigInteger((this.clauses).Count))];
      (this).falseLiteralsCount = _nw5;
      var _nw6 = new BigInteger[(int)(new BigInteger((this.clauses).Count))];
      (this).literalsCount = _nw6;
      var _nw7 = new bool[(int)(new BigInteger((clauses).Count))];
      (this).satisfiedClauses = _nw7;
      { }
      var _nw8 = Dafny.ArrayHelpers.InitNewArray1<Dafny.Sequence<BigInteger>>(Dafny.Sequence<BigInteger>.Empty, (variablesCount));
      (this).positiveLiteralsToClauses = _nw8;
      var _nw9 = Dafny.ArrayHelpers.InitNewArray1<Dafny.Sequence<BigInteger>>(Dafny.Sequence<BigInteger>.Empty, (variablesCount));
      (this).negativeLiteralsToClauses = _nw9;
      { }
      { }
      (this).createTFLArrays();
      { }
      { }
      { }
      { }
      (this).createPositiveLiteralsToClauses();
      { }
      (this).createNegativeLiteralsToClauses();
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      (this).createSatisfiedClausesArray();
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public void createTFLArrays()
    {
      var _this = this;
    TAIL_CALL_START: ;
      BigInteger _448_i;
      _448_i = new BigInteger(0);
      while ((_448_i) < (new BigInteger((_this.clauses).Count))) {
        var _arr0 = _this.literalsCount;
        _arr0[(int)((_448_i))] = new BigInteger(((_this.clauses).Select(_448_i)).Count);
        { }
        var _arr1 = _this.trueLiteralsCount;
        _arr1[(int)((_448_i))] = new BigInteger(0);
        { }
        var _arr2 = _this.falseLiteralsCount;
        _arr2[(int)((_448_i))] = new BigInteger(0);
        _448_i = (_448_i) + (new BigInteger(1));
      }
    }
    public bool isUnitClause(BigInteger index) {
      return (((this.trueLiteralsCount)[(int)(index)]) == (new BigInteger(0))) && ((((this.literalsCount)[(int)(index)]) - ((this.falseLiteralsCount)[(int)(index)])) == (new BigInteger(1)));
    }
    public bool isEmptyClause(BigInteger index) {
      return ((this.literalsCount)[(int)(index)]) == ((this.falseLiteralsCount)[(int)(index)]);
    }
    public void createPositiveLiteralsToClauses()
    {
      var _this = this;
    TAIL_CALL_START: ;
      BigInteger _449_variable;
      _449_variable = new BigInteger(0);
      while ((_449_variable) < (_this.variablesCount)) {
        var _arr3 = _this.positiveLiteralsToClauses;
        _arr3[(int)((_449_variable))] = Dafny.Sequence<BigInteger>.FromElements();
        BigInteger _450_clauseIndex;
        _450_clauseIndex = new BigInteger(0);
        while ((_450_clauseIndex) < (new BigInteger((_this.clauses).Count))) {
          if (((_this.clauses).Select(_450_clauseIndex)).Contains((_449_variable) + (new BigInteger(1)))) {
            var _arr4 = _this.positiveLiteralsToClauses;
            _arr4[(int)((_449_variable))] = ((_this.positiveLiteralsToClauses)[(int)(_449_variable)]).Concat(Dafny.Sequence<BigInteger>.FromElements(_450_clauseIndex));
          }
          _450_clauseIndex = (_450_clauseIndex) + (new BigInteger(1));
        }
        _449_variable = (_449_variable) + (new BigInteger(1));
      }
    }
    public void createNegativeLiteralsToClauses()
    {
      var _this = this;
    TAIL_CALL_START: ;
      BigInteger _451_variable;
      _451_variable = new BigInteger(0);
      while ((_451_variable) < (_this.variablesCount)) {
        var _arr5 = _this.negativeLiteralsToClauses;
        _arr5[(int)((_451_variable))] = Dafny.Sequence<BigInteger>.FromElements();
        BigInteger _452_clauseIndex;
        _452_clauseIndex = new BigInteger(0);
        while ((_452_clauseIndex) < (new BigInteger((_this.clauses).Count))) {
          if (((_this.clauses).Select(_452_clauseIndex)).Contains(((new BigInteger(0)) - (_451_variable)) - (new BigInteger(1)))) {
            var _arr6 = _this.negativeLiteralsToClauses;
            _arr6[(int)((_451_variable))] = ((_this.negativeLiteralsToClauses)[(int)(_451_variable)]).Concat(Dafny.Sequence<BigInteger>.FromElements(_452_clauseIndex));
          }
          _452_clauseIndex = (_452_clauseIndex) + (new BigInteger(1));
        }
        _451_variable = (_451_variable) + (new BigInteger(1));
      }
    }
    public void createSatisfiedClausesArray()
    {
      var _this = this;
    TAIL_CALL_START: ;
      BigInteger _453_i;
      _453_i = new BigInteger(0);
      while ((_453_i) < (new BigInteger((_this.clauses).Count))) {
        { }
        { }
        { }
        { }
        var _arr7 = _this.satisfiedClauses;
        _arr7[(int)((_453_i))] = false;
        _453_i = (_453_i) + (new BigInteger(1));
      }
    }
    public void newLayerOnStack()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this.stack).createNewLayer();
      { }
      { }
    }
    public void undoLayerOnStack()
    {
      BigInteger _454_k;
      _454_k = new BigInteger(0);
      Dafny.Sequence<_System.Tuple2<BigInteger,bool>> _455_layer;
      _455_layer = (this.stack.stack)[(int)((this.stack.size) - (new BigInteger(1)))];
      var _arr8 = this.stack.stack;
      var _index0 = (this.stack.size) - (new BigInteger(1));
      _arr8[(int)(_index0)] = Dafny.Sequence<_System.Tuple2<BigInteger,bool>>.FromElements();
      var _obj0 = this.stack;
      _obj0.size = (this.stack.size) - (new BigInteger(1));
      while ((_454_k) < (new BigInteger((_455_layer).Count))) {
        _System.Tuple2<BigInteger,bool> _456_x;
        _456_x = (_455_layer).Select(_454_k);
        _454_k = (_454_k) + (new BigInteger(1));
        _System.Tuple2<BigInteger,bool> _let_tmp_rhs5 = _456_x;
        BigInteger _457_variable = ((_System.Tuple2<BigInteger,bool>)_let_tmp_rhs5)._0;
        bool _458_value = ((_System.Tuple2<BigInteger,bool>)_let_tmp_rhs5)._1;
        { }
        var _arr9 = this.truthAssignment;
        _arr9[(int)((_457_variable))] = (new BigInteger(0)) - (new BigInteger(1));
        { }
        { }
        { }
        { }
        { }
        Dafny.Sequence<BigInteger> _459_positivelyImpactedClauses;
        _459_positivelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_457_variable)];
        Dafny.Sequence<BigInteger> _460_negativelyImpactedClauses;
        _460_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_457_variable)];
        if (!(_458_value)) {
          _460_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_457_variable)];
          _459_positivelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_457_variable)];
        }
        { }
        { }
        { }
        BigInteger _461_i;
        _461_i = new BigInteger(0);
        while ((_461_i) < (new BigInteger((_459_positivelyImpactedClauses).Count))) {
          BigInteger _462_clauseIndex;
          _462_clauseIndex = (_459_positivelyImpactedClauses).Select(_461_i);
          Dafny.Sequence<BigInteger> _463_clause;
          _463_clause = (this.clauses).Select(_462_clauseIndex);
          { }
          { }
          var _arr10 = this.trueLiteralsCount;
          _arr10[(int)((_462_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_462_clauseIndex)]) - (new BigInteger(1));
          if (((this.trueLiteralsCount)[(int)(_462_clauseIndex)]) == (new BigInteger(0))) {
            { }
            var _arr11 = this.satisfiedClauses;
            _arr11[(int)((_462_clauseIndex))] = false;
          } else { }
          _461_i = (_461_i) + (new BigInteger(1));
        }
        _461_i = new BigInteger(0);
        while ((_461_i) < (new BigInteger((_460_negativelyImpactedClauses).Count))) {
          BigInteger _464_clauseIndex;
          _464_clauseIndex = (_460_negativelyImpactedClauses).Select(_461_i);
          { }
          var _arr12 = this.falseLiteralsCount;
          _arr12[(int)((_464_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_464_clauseIndex)]) - (new BigInteger(1));
          _461_i = (_461_i) + (new BigInteger(1));
        }
      }
    }
    public void setVariable(BigInteger variable, bool @value)
    {
      { }
      _System.Tuple2<BigInteger,bool> _465_el;
      _465_el = @_System.Tuple2<BigInteger,bool>.create(variable, @value);
      BigInteger _466_iL;
      _466_iL = (this.stack.size) - (new BigInteger(1));
      { }
      var _arr13 = this.stack.stack;
      _arr13[(int)((_466_iL))] = ((this.stack.stack)[(int)(_466_iL)]).Concat(Dafny.Sequence<_System.Tuple2<BigInteger,bool>>.FromElements(_465_el));
      { }
      if (@value) {
        var _arr14 = this.truthAssignment;
        _arr14[(int)((variable))] = new BigInteger(1);
      } else {
        var _arr15 = this.truthAssignment;
        _arr15[(int)((variable))] = new BigInteger(0);
      }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      BigInteger _467_trueLiteral;
      _467_trueLiteral = (variable) + (new BigInteger(1));
      BigInteger _468_falseLiteral;
      _468_falseLiteral = ((new BigInteger(0)) - (variable)) - (new BigInteger(1));
      if (!(@value)) {
        _467_trueLiteral = ((new BigInteger(0)) - (variable)) - (new BigInteger(1));
        _468_falseLiteral = (variable) + (new BigInteger(1));
      }
      { }
      { }
      BigInteger _469_i;
      _469_i = new BigInteger(0);
      Dafny.Sequence<BigInteger> _470_impactedClauses;
      _470_impactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      Dafny.Sequence<BigInteger> _471_impactedClauses_k;
      _471_impactedClauses_k = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _470_impactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
        _471_impactedClauses_k = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      { }
      { }
      { }
      { }
      while ((_469_i) < (new BigInteger((_470_impactedClauses).Count))) {
        BigInteger _472_clauseIndex;
        _472_clauseIndex = (_470_impactedClauses).Select(_469_i);
        { }
        var _arr16 = this.trueLiteralsCount;
        _arr16[(int)((_472_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_472_clauseIndex)]) + (new BigInteger(1));
        var _arr17 = this.satisfiedClauses;
        _arr17[(int)((_472_clauseIndex))] = true;
        { }
        { }
        _469_i = (_469_i) + (new BigInteger(1));
      }
      { }
      { }
      BigInteger _473_i_k;
      _473_i_k = new BigInteger(0);
      { }
      { }
      { }
      while ((_473_i_k) < (new BigInteger((_471_impactedClauses_k).Count))) {
        BigInteger _474_clauseIndex;
        _474_clauseIndex = (_471_impactedClauses_k).Select(_473_i_k);
        { }
        var _arr18 = this.falseLiteralsCount;
        _arr18[(int)((_474_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_474_clauseIndex)]) + (new BigInteger(1));
        _473_i_k = (_473_i_k) + (new BigInteger(1));
      }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public bool hasEmptyClause() {
      if (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((this.clauses).Count)), false, (((_475_i) => {
        return (((new BigInteger(0)) <= (_475_i)) && ((_475_i) < (new BigInteger((this.clauses).Count)))) && (((this.falseLiteralsCount)[(int)(_475_i)]) == ((this.literalsCount)[(int)(_475_i)]));
      })))) {
        return Dafny.Helpers.Let<int,bool>(0, _let_dummy_0 =>  {
          BigInteger _476_i = BigInteger.Zero;
          foreach (var _assign_such_that_0 in Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((this.clauses).Count))) { _476_i = _assign_such_that_0;
            if ((((new BigInteger(0)) <= (_476_i)) && ((_476_i) < (new BigInteger((this.clauses).Count)))) && (((this.falseLiteralsCount)[(int)(_476_i)]) == ((this.literalsCount)[(int)(_476_i)]))) {
              goto after__ASSIGN_SUCH_THAT_0;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 837)");
        after__ASSIGN_SUCH_THAT_0: ;
          return true;
        });
      } else  {
        return false;
      }
    }
    public bool isEmpty() {
      if (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((this.clauses).Count)), false, (((_477_i) => {
        return (((new BigInteger(0)) <= (_477_i)) && ((_477_i) < (new BigInteger((this.clauses).Count)))) && (((this.trueLiteralsCount)[(int)(_477_i)]) == (new BigInteger(0)));
      })))) {
        return Dafny.Helpers.Let<int,bool>(0, _let_dummy_1 =>  {
          BigInteger _478_i = BigInteger.Zero;
          foreach (var _assign_such_that_1 in Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((this.clauses).Count))) { _478_i = _assign_such_that_1;
            if ((((new BigInteger(0)) <= (_478_i)) && ((_478_i) < (new BigInteger((this.clauses).Count)))) && (((this.trueLiteralsCount)[(int)(_478_i)]) == (new BigInteger(0)))) {
              goto after__ASSIGN_SUCH_THAT_1;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 855)");
        after__ASSIGN_SUCH_THAT_1: ;
          return false;
        });
      } else  {
        return true;
      }
    }
    public void chooseLiteral(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      BigInteger _479_i;
      foreach (var _assign_such_that_2 in Dafny.Helpers.IntegerRange(new BigInteger(0), new BigInteger((_this.clauses).Count))) { _479_i = _assign_such_that_2;
        if ((((new BigInteger(0)) <= (_479_i)) && ((_479_i) < (new BigInteger((_this.clauses).Count)))) && (((_this.trueLiteralsCount)[(int)(_479_i)]) == (new BigInteger(0)))) {
          goto after__ASSIGN_SUCH_THAT_2;
        }
      }
      throw new System.Exception("assign-such-that search produced no value (line 992)");
    after__ASSIGN_SUCH_THAT_2: ;
      { }
      { }
      BigInteger _480_literal;
      foreach (var _assign_such_that_3 in ((_this.clauses).Select(_479_i)).Elements) { _480_literal = _assign_such_that_3;
        if ((((_this.clauses).Select(_479_i)).Contains(_480_literal)) && (((_this.truthAssignment)[(int)((_this).getVariableFromLiteral(_480_literal))]) == ((new BigInteger(0)) - (new BigInteger(1))))) {
          goto after__ASSIGN_SUCH_THAT_3;
        }
      }
      throw new System.Exception("assign-such-that search produced no value (line 995)");
    after__ASSIGN_SUCH_THAT_3: ;
      x = _480_literal;
      return;
    }
    public void setLiteral(BigInteger literal, bool @value)
    {
      { }
      { }
      { }
      BigInteger _481_variable;
      _481_variable = (this).getVariableFromLiteral(literal);
      bool _482_value_k;
      _482_value_k = ((literal) > (new BigInteger(0))) ? (@value) : (!(@value));
      (this).setVariable(_481_variable, _482_value_k);
      { }
      Dafny.Sequence<BigInteger> _483_negativelyImpactedClauses;
      _483_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_481_variable)];
      BigInteger _484_k;
      _484_k = new BigInteger(0);
      { }
      { }
      { }
      while ((_484_k) < (new BigInteger((_483_negativelyImpactedClauses).Count))) {
        BigInteger _485_clauseIndex;
        _485_clauseIndex = (_483_negativelyImpactedClauses).Select(_484_k);
        Dafny.Sequence<BigInteger> _486_clause;
        _486_clause = (this.clauses).Select(_485_clauseIndex);
        { }
        if ((((this.trueLiteralsCount)[(int)(_485_clauseIndex)]) == (new BigInteger(0))) && ((((this.falseLiteralsCount)[(int)(_485_clauseIndex)]) + (new BigInteger(1))) == ((this.literalsCount)[(int)(_485_clauseIndex)]))) {
          { }
          BigInteger _487_literal;
          foreach (var _assign_such_that_4 in (_486_clause).Elements) { _487_literal = _assign_such_that_4;
            if (((_486_clause).Contains(_487_literal)) && (((this.truthAssignment)[(int)((this).getVariableFromLiteral(_487_literal))]) == ((new BigInteger(0)) - (new BigInteger(1))))) {
              goto after__ASSIGN_SUCH_THAT_4;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 1079)");
        after__ASSIGN_SUCH_THAT_4: ;
          { }
          { }
          { }
          (this).setLiteral(_487_literal, true);
          { }
          { }
          { }
          { }
          { }
        }
        _484_k = (_484_k) + (new BigInteger(1));
      }
      { }
      { }
    }
    public void render(Dafny.Sequence<BigInteger> truthAssignment)
    {
      var _this = this;
    TAIL_CALL_START: ;
      BigInteger _488_clauseIndex;
      _488_clauseIndex = new BigInteger(0);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Solution:\n"));
      Dafny.Helpers.Print(truthAssignment);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n\nClauses:\n"));
      while ((_488_clauseIndex) < (new BigInteger((_this.clauses).Count))) {
        Dafny.Sequence<BigInteger> _489_clause;
        _489_clause = (_this.clauses).Select(_488_clauseIndex);
        { }
        BigInteger _490_literalIndex;
        _490_literalIndex = new BigInteger(0);
        while ((_490_literalIndex) < (new BigInteger((_489_clause).Count))) {
          BigInteger _491_literal;
          _491_literal = (_489_clause).Select(_490_literalIndex);
          { }
          Dafny.Helpers.Print(_491_literal);
          { }
          if (((_491_literal) < (new BigInteger(0))) && (((truthAssignment).Select(((new BigInteger(0)) - (_491_literal)) - (new BigInteger(1)))) == (new BigInteger(0)))) {
            Dafny.Helpers.Print('*');
          } else if (((_491_literal) > (new BigInteger(0))) && (((truthAssignment).Select((_491_literal) - (new BigInteger(1)))) == (new BigInteger(1)))) {
            Dafny.Helpers.Print('*');
          }
          Dafny.Helpers.Print(' ');
          _490_literalIndex = (_490_literalIndex) + (new BigInteger(1));
        }
        Dafny.Helpers.Print('\n');
        _488_clauseIndex = (_488_clauseIndex) + (new BigInteger(1));
      }
    }
  }



  public interface DataStructures {
    BigInteger variablesCount { get; set; }
    Dafny.Sequence<Dafny.Sequence<BigInteger>> clauses { get; set; }
    Stack stack { get; set; }
    BigInteger[] truthAssignment { get; set; }
    bool[] satisfiedClauses { get; set; }
    BigInteger[] trueLiteralsCount { get; set; }
    BigInteger[] falseLiteralsCount { get; set; }
    BigInteger[] literalsCount { get; set; }
    Dafny.Sequence<BigInteger>[] positiveLiteralsToClauses { get; set; }
    Dafny.Sequence<BigInteger>[] negativeLiteralsToClauses { get; set; }
    _System.Tuple2<BigInteger,BigInteger> convertLVtoVI(BigInteger literal, bool @value);
    BigInteger getVariableFromLiteral(BigInteger literal);
  }
  public class _Companion_DataStructures {
  }



  public partial class Stack {
    public BigInteger size = BigInteger.Zero;
    public Dafny.Sequence<_System.Tuple2<BigInteger,bool>>[] stack = new Dafny.Sequence<_System.Tuple2<BigInteger,bool>>[0];
    public BigInteger variablesCount = BigInteger.Zero;
    public void __ctor(BigInteger varCount)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).size = new BigInteger(0);
      (_this).variablesCount = varCount;
      var _nw10 = Dafny.ArrayHelpers.InitNewArray1<Dafny.Sequence<_System.Tuple2<BigInteger,bool>>>(Dafny.Sequence<_System.Tuple2<BigInteger,bool>>.Empty, (varCount));
      (_this).stack = _nw10;
      { }
      BigInteger _492_i;
      _492_i = new BigInteger(0);
      while ((_492_i) < (new BigInteger((_this.stack).Length))) {
        var _arr19 = _this.stack;
        _arr19[(int)((_492_i))] = Dafny.Sequence<_System.Tuple2<BigInteger,bool>>.FromElements();
        _492_i = (_492_i) + (new BigInteger(1));
      }
    }
    public void createNewLayer()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).size = (_this.size) + (new BigInteger(1));
      { }
    }
  }
} // end of namespace _module
