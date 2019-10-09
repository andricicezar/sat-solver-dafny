include "concerns/seq-predicates.dfy"
include "utils.dfy"
include "stack.dfy"
trait DataStructures { 
  var variablesCount : int;
  var clauses : seq<seq<int>>;
  var stack : Stack;
  var truthAssignment : array<int>; // from 0 to variablesCount - 1, values: -1, 0, 1
  var trueLiteralsCount : array<int>; // from 0 to |clauses| - 1
  var falseLiteralsCount : array<int>; // from 0 to |clauses| - 1
  var positiveLiteralsToClauses : array<seq<int>>; // from 0 to variablesCount - 1
  var negativeLiteralsToClauses : array<seq<int>>; // frm 0 to variablesCount - 1
  predicate validVariablesCount() 
    reads this;
  {
    variablesCount > 0
  }
  predicate validClauses() 
    requires validVariablesCount();
    reads this;
  {
    |clauses| > 0 &&
    forall clause :: (clause in clauses) ==>
      validClause(clause)
  }
  predicate validClause(clause : seq<int>) 
    requires validVariablesCount();
    reads this;
  {
    (forall x, y :: 0 <= x < y < |clause| ==>
      clause[x] < clause[y]) 
    &&
    (forall literal :: (literal in clause) ==>
      validLiteral(literal))
  }
  predicate validLiteral(literal : int) 
    requires validVariablesCount();
    reads this;
  {
    if literal == 0 then false
    else if -variablesCount <= literal <= variablesCount then true
    else false
  }
  predicate validVariable(variable : int)
    reads this;
    requires validVariablesCount();
  {
    0 <= variable < variablesCount
  }
  predicate validStack()
    reads this, stack, stack.stack;
    requires validVariablesCount();
  {
    stack.valid() && stack.variablesCount == this.variablesCount
  }
  function convertIntToBool(x : int) : bool
  {
    if x == 0 then false
    else true
  }
  predicate validValuesTruthAssignment(truthAssignment : seq<int>)
    reads this;
    requires validVariablesCount();
  {
    |truthAssignment| == variablesCount &&
    (forall i :: 0 <= i < |truthAssignment| ==>
      -1 <= truthAssignment[i] <= 1) 
  }
  predicate validTruthAssignment()
    reads this, stack, stack.stack, truthAssignment;
    requires validVariablesCount();
    requires validStack();
  {
    validValuesTruthAssignment(truthAssignment[..])
    &&
    (forall i :: 0 <= i < truthAssignment.Length && truthAssignment[i] != -1 ==>
      (i, convertIntToBool(truthAssignment[i])) in stack.contents)
    &&
    (forall i :: 0 <= i < truthAssignment.Length && truthAssignment[i] == -1 ==>
      (i, false) !in stack.contents && (i, true) !in stack.contents)
  }
  predicate isClauseSatisfied(truthAssignment : seq<int>, clauseIndex : int) 
    reads this;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires 0 <= clauseIndex < |clauses|;
  {
    assert validClause(clauses[clauseIndex]);
    exists literal :: (literal in clauses[clauseIndex]) &&
      getLiteralValue(truthAssignment, literal) == 1
  }
  function method convertLVtoVI(literal : int, value : bool) : (int, int) 
    reads this; 
    requires validVariablesCount();
    requires validLiteral(literal);
    ensures validVariable(convertLVtoVI(literal, value).0);
    ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal);
    ensures convertLVtoVI(literal, value).1 in [0,1];
  {
    var variable := getVariableFromLiteral(literal);
    var v := if value then 1 else 0;
    var val := if literal < 0 then 1-v else v;
    (variable, val)
  }
  function method getVariableFromLiteral(literal : int) : int 
    reads this;
    requires validVariablesCount();
    requires validLiteral(literal);
    ensures validVariable(getVariableFromLiteral(literal));
  {
    Utils.abs(literal)-1
  }
  function getLiteralValue(truthAssignment : seq<int>, literal : int) : int
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validLiteral(literal);
  {
    var variable := Utils.abs(literal)-1;
    if (truthAssignment[variable] == -1) then -1
    else if literal < 0 then 1-truthAssignment[variable]
    else truthAssignment[variable]
  }
  predicate validTrueLiteralsCount(truthAssignment : seq<int>)
    reads this, trueLiteralsCount;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
    trueLiteralsCount.Length == |clauses| &&
    forall i :: 0 <= i < |clauses| ==>
      0 <= trueLiteralsCount[i] == countTrueLiterals(truthAssignment, clauses[i])
  }
  function countUnsetVariables(truthAssignment : seq<int>) : int
    ensures 0 <= countUnsetVariables(truthAssignment) <= |truthAssignment|;
  {
    if |truthAssignment| == 0 then 0
    else (
      var ok := if truthAssignment[0] == -1 then 1 else 0;
      ok + countUnsetVariables(truthAssignment[1..])
    )
  }
  function countTrueLiterals(truthAssignment : seq<int>, clause : seq<int>) : int
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    ensures 0 <= countTrueLiterals(truthAssignment, clause) <= |clause|;
  {
    if |clause| == 0 then 0
    else 
      var ok := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0;
      ok + countTrueLiterals(truthAssignment, clause[1..])
  }
  lemma prop_countTrueLiterals_initialTruthAssignment(truthAssignment : seq<int>, clause : seq<int>)
    requires validVariablesCount();
    requires validStack();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires forall j :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1;
    ensures countTrueLiterals(truthAssignment, clause) == 0;
  {
    assert forall literal :: literal in clause ==>
      getLiteralValue(truthAssignment, literal) == -1;
  }
  lemma countTrueLiterals0_noLiteralsTrue(truthAssignment : seq<int>, clause : seq<int>) 
    requires validVariablesCount();
    requires validClause(clause);
    requires validValuesTruthAssignment(truthAssignment);
    requires countTrueLiterals(truthAssignment, clause) == 0;
    ensures forall literal :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1;
  {
      var k := 0;
      while (k < |clause|) 
        invariant -1 <= k <= |clause|;
        invariant forall k' :: 0 <= k' < k ==> 
          getLiteralValue(truthAssignment, clause[k']) != 1;
        invariant countTrueLiterals(truthAssignment, clause[k..]) == 0;
        decreases |clause| - k;
      {
        k := k + 1;
      }
  }
  lemma countTrueLiteralsX_existsTrueLiteral(truthAssignment : seq<int>, clause : seq<int>) 
    requires validVariablesCount();
    requires validClause(clause);
    requires validValuesTruthAssignment(truthAssignment);
    requires countTrueLiterals(truthAssignment, clause) > 0;
    ensures exists literal :: literal in clause && getLiteralValue(truthAssignment, literal) == 1;
  {
    if (countTrueLiterals(truthAssignment, clause) == 0) {
      countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);
      assert forall literal :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1;
    } else {
      if (getLiteralValue(truthAssignment, clause[0]) != 1) {
        countTrueLiteralsX_existsTrueLiteral(truthAssignment, clause[1..]);  
      } else {
      }
    }
  }
  predicate validFalseLiteralsCount(truthAssignment : seq<int>)
    reads this, falseLiteralsCount;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
    falseLiteralsCount.Length == |clauses| &&
    forall i :: 0 <= i < |clauses| ==>
      0 <= falseLiteralsCount[i] == countFalseLiterals(truthAssignment, clauses[i])
  }
  function countFalseLiterals(truthAssignment : seq<int>, clause : seq<int>) : int
    reads this;
    requires validVariablesCount();
    requires validClause(clause);
    requires validValuesTruthAssignment(truthAssignment);
    ensures 0 <= countFalseLiterals(truthAssignment, clause) <= |clause|;
  {
    if |clause| == 0 then 0
    else 
      var ok := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0;
      ok + countFalseLiterals(truthAssignment, clause[1..])
  }
  lemma prop_countFalseLiterals_initialTruthAssignment(truthAssignment : seq<int>, clause : seq<int>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires forall j :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1;
    ensures countFalseLiterals(truthAssignment, clause) == 0;
  {
    assert forall literal :: literal in clause ==>
              getLiteralValue(truthAssignment, literal) == -1;
  }
  predicate validPositiveLiteralsToClauses()
    reads this, positiveLiteralsToClauses;
    requires validVariablesCount();
    requires validClauses();
  {
    positiveLiteralsToClauses.Length == variablesCount &&
    (forall variable :: 0 <= variable < positiveLiteralsToClauses.Length ==> 
      validPositiveLiteralToClause(variable, positiveLiteralsToClauses[variable]))
  }
  predicate validPositiveLiteralToClause(variable : int, s : seq<int>) 
    reads this; 
    requires validVariablesCount();
    requires validClauses();
    requires 0 <= variable < variablesCount;
  {
    SeqPredicates.valuesBoundedBy(s, 0, |clauses|) &&
    SeqPredicates.orderedAsc(s) &&
    (forall clauseIndex :: clauseIndex in s ==>
      variable+1 in clauses[clauseIndex]) &&
    (forall clauseIndex :: 0 <= clauseIndex < |clauses| && clauseIndex !in s ==>
      variable+1 !in clauses[clauseIndex])
  }
  predicate validNegativeLiteralsToClauses()
    reads this, negativeLiteralsToClauses;
    requires validVariablesCount();
    requires validClauses();
  {
    negativeLiteralsToClauses.Length == variablesCount &&
    forall v :: 0 <= v < negativeLiteralsToClauses.Length ==>
      validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
  }
  predicate validNegativeLiteralsToClause(variable : int, s : seq<int>)
    reads this;
    requires validVariablesCount();
    requires validClauses();
    requires 0 <= variable < variablesCount;
  {
    SeqPredicates.valuesBoundedBy(s, 0, |clauses|) &&
    SeqPredicates.orderedAsc(s) &&
    (forall clauseIndex :: clauseIndex in s ==>
      -variable-1 in clauses[clauseIndex]) &&
    (forall clauseIndex :: 0 <= clauseIndex < |clauses| && clauseIndex !in s ==>
      -variable-1 !in clauses[clauseIndex])
  }
  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
  {
    (truthAssignment != trueLiteralsCount) &&
    (truthAssignment != falseLiteralsCount) &&
    (trueLiteralsCount != falseLiteralsCount) &&
    (positiveLiteralsToClauses != negativeLiteralsToClauses)
  }
  predicate valid() 
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
  {
    validReferences() &&
    validVariablesCount() &&
    validClauses() &&
    validStack() &&
    validTruthAssignment() &&
    validTrueLiteralsCount(truthAssignment[..]) &&
    validFalseLiteralsCount(truthAssignment[..]) &&
    validPositiveLiteralsToClauses() &&
    validNegativeLiteralsToClauses()
  }
  lemma clausesNotImpacted_TFArraysSame(oldTau : seq<int>, newTau : seq<int>, variable : int, impactedClauses : seq<int>, impactedClauses' : seq<int>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validClauses();
    requires validTrueLiteralsCount(oldTau);
    requires validFalseLiteralsCount(oldTau);
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex]);
    requires validVariable(variable);
    requires newTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses);
    requires newTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses');
    requires newTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses');
    requires newTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses);
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    ensures forall clauseIndex :: 0 <= clauseIndex < |clauses|
      && clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex]) ==
          countTrueLiterals(newTau, clauses[clauseIndex]);
    ensures forall clauseIndex :: 0 <= clauseIndex < |clauses|
      && clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex]) ==
          countFalseLiterals(newTau, clauses[clauseIndex]);
  {
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    forall clauseIndex | 0 <= clauseIndex < |clauses|
      ensures clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex])
          == countTrueLiterals(newTau, clauses[clauseIndex]);
      ensures clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex])
          == countFalseLiterals(newTau, clauses[clauseIndex]);
    {
      var clause := clauses[clauseIndex];
      var k := |clause|-1;
      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant clauseIndex !in impactedClauses ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 1 <==>
              getLiteralValue(oldTau, clause[j]) == 1);
        invariant clauseIndex !in impactedClauses ==> forall j :: k < j <= |clause| ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 0 <==>
              getLiteralValue(oldTau, clause[j]) == 0);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j <= |clause| ==>
            countFalseLiterals(oldTau, clause[j..])
              == countFalseLiterals(newTau, clause[j..]);
        decreases k;
      {
        if (clauseIndex !in impactedClauses) {
          assert clause[k] != trueLiteral;
          if (clause[k] == falseLiteral) {
            assert getLiteralValue(newTau, clause[k]) == 0;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 1 <==>
              getLiteralValue(oldTau, clause[k]) == 1;
          }
        } else if (clauseIndex !in impactedClauses') {
          assert clause[k] != falseLiteral;
          if (clause[k] == trueLiteral) {
            assert getLiteralValue(newTau, clause[k]) == 1;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 0 <==>
              getLiteralValue(oldTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }
  lemma setVariable_countTrueLiteralsIncreasesWithOne(oldTau : seq<int>, newTau : seq<int>, variable : int, clause : seq<int>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires newTau[variable] == 1 ==> variable+1 in clause;
    requires newTau[variable] == 0 ==> -variable-1 in clause;
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) + 1;
  {
    var k := |clause|-1;
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall j :: k < j < |clause| && clause[j] > trueLiteral ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);
      invariant forall j :: k < j < |clause| && clause[j] <= trueLiteral ==>
            countTrueLiterals(oldTau, clause[j..])+1
              == countTrueLiterals(newTau, clause[j..]);
      decreases k;
    {
      if (clause[k] == trueLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == -1;
        assert getLiteralValue(newTau, clause[k]) == 1;
      } else if (clause[k] == falseLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == -1;
        assert getLiteralValue(newTau, clause[k]) == 0;
      } else {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }
  lemma setVariable_countFalseLiteralsIncreasesWithOne(oldTau : seq<int>, newTau : seq<int>, variable : int, clause : seq<int>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires newTau[variable] == 1 ==> -variable-1 in clause;
    requires newTau[variable] == 0 ==> variable+1 in clause;
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) + 1;
  {
    var k := |clause|-1;
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (newTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall j :: k < j < |clause| && clause[j] > falseLiteral ==>
            countFalseLiterals(oldTau, clause[j..]) ==
              countFalseLiterals(newTau, clause[j..]);
      invariant forall j :: k < j < |clause| && clause[j] <= falseLiteral ==>
            countFalseLiterals(oldTau, clause[j..])+1 ==
              countFalseLiterals(newTau, clause[j..]);
      decreases k;
    {
      if (clause[k] == falseLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == -1;
        assert getLiteralValue(newTau, clause[k]) == 0;
      } else if (clause[k] == trueLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == -1;
        assert getLiteralValue(newTau, clause[k]) == 1;
      } else {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }
  lemma unsetVariable_countTrueLiteralsDecreasesWithOne(
    oldTau : seq<int>,
    newTau : seq<int>,
    variable : int,
    clause : seq<int>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires oldTau[variable] == 1 ==> variable+1 in clause;
    requires oldTau[variable] == 0 ==> -variable-1 in clause;
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;
    ensures countTrueLiterals(newTau, clause) 
      == countTrueLiterals(oldTau, clause) - 1;
  {
    var k := |clause|-1;
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall j :: k < j < |clause| && clause[j] > trueLiteral ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);
      invariant forall j :: k < j < |clause| && clause[j] <= trueLiteral ==>
            countTrueLiterals(oldTau, clause[j..])-1
              == countTrueLiterals(newTau, clause[j..]);
      decreases k;
    {
      if (clause[k] == trueLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == 1;
      } else if (clause[k] == falseLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == 0;
      } else {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }
  lemma unsetVariable_countFalseLiteralsDecreasesWithOne(
    oldTau : seq<int>,
    newTau : seq<int>,
    variable : int,
    clause : seq<int>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validVariable(variable);
    requires validClause(clause);
    requires oldTau[variable] == 1 ==> -variable-1 in clause;
    requires oldTau[variable] == 0 ==> variable+1 in clause;
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;
    ensures countFalseLiterals(newTau, clause)
              == countFalseLiterals(oldTau, clause) - 1;
  {
    var k := |clause|-1;
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall j :: k < j < |clause| && clause[j] > falseLiteral ==>
            countFalseLiterals(oldTau, clause[j..]) ==
              countFalseLiterals(newTau, clause[j..]);
      invariant forall j :: k < j < |clause| && clause[j] <= falseLiteral ==>
            countFalseLiterals(oldTau, clause[j..])-1 ==
              countFalseLiterals(newTau, clause[j..]);
      decreases k;
    {
      if (clause[k] == falseLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == 0;
        assert getLiteralValue(newTau, clause[k]) == -1;
      } else if (clause[k] == trueLiteral) {
        assert getLiteralValue(oldTau, clause[k]) == 1;
        assert getLiteralValue(newTau, clause[k]) == -1;
      } else {
        assert oldTau[getVariableFromLiteral(clause[k])]
          == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }
  lemma undoImpactedClauses_TFSArraysModified(
    oldTau : seq<int>,
    newTau : seq<int>,
    variable : int,
    impactedClauses : seq<int>,
    impactedClauses' : seq<int>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires validClauses();
    requires validTrueLiteralsCount(oldTau);
    requires validFalseLiteralsCount(oldTau);
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      validClause(clauses[clauseIndex]);
    requires validVariable(variable);
    requires oldTau[variable] == 1 ==>
      validPositiveLiteralToClause(variable, impactedClauses);
    requires oldTau[variable] == 1 ==>
      validNegativeLiteralsToClause(variable, impactedClauses');
    requires oldTau[variable] == 0 ==>
      validPositiveLiteralToClause(variable, impactedClauses');
    requires oldTau[variable] == 0 ==>
      validNegativeLiteralsToClause(variable, impactedClauses);
    requires forall x :: 0 <= x < |oldTau| && x != variable
      ==> oldTau[x] == newTau[x];
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      countTrueLiterals(oldTau, clauses[clauseIndex]) ==
        trueLiteralsCount[clauseIndex];
    requires forall clauseIndex :: 0 <= clauseIndex < |clauses| ==>
      countFalseLiterals(oldTau, clauses[clauseIndex]) ==
        falseLiteralsCount[clauseIndex];
    requires oldTau[variable] in [0, 1];
    requires newTau[variable] == -1;
    ensures forall clauseIndex :: 0 <= clauseIndex < |clauses|
      && clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex]) ==
          countTrueLiterals(newTau, clauses[clauseIndex]);
    ensures forall clauseIndex :: 0 <= clauseIndex < |clauses|
      && clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex]) ==
          countFalseLiterals(newTau, clauses[clauseIndex]);
  {
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (oldTau[variable] == 0) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    forall clauseIndex | 0 <= clauseIndex < |clauses|
      ensures clauseIndex !in impactedClauses ==>
        countTrueLiterals(oldTau, clauses[clauseIndex])
          == countTrueLiterals(newTau, clauses[clauseIndex]);
      ensures clauseIndex !in impactedClauses' ==>
        countFalseLiterals(oldTau, clauses[clauseIndex])
          == countFalseLiterals(newTau, clauses[clauseIndex]);
    {
      var clause := clauses[clauseIndex];
      var k := |clause|-1;
      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant clauseIndex !in impactedClauses ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 1 <==>
              getLiteralValue(oldTau, clause[j]) == 1);
        invariant clauseIndex !in impactedClauses ==> forall j :: k < j <= |clause| ==>
            countTrueLiterals(oldTau, clause[j..])
              == countTrueLiterals(newTau, clause[j..]);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j < |clause| ==>
            (getLiteralValue(newTau, clause[j]) == 0 <==>
              getLiteralValue(oldTau, clause[j]) == 0);
        invariant clauseIndex !in impactedClauses' ==>
          forall j :: k < j <= |clause| ==>
            countFalseLiterals(oldTau, clause[j..])
              == countFalseLiterals(newTau, clause[j..]);
        decreases k;
      {
        if (clauseIndex !in impactedClauses) {
          assert clause[k] != trueLiteral;
          if (clause[k] == falseLiteral) {
            assert getLiteralValue(oldTau, clause[k]) == 0;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 1 <==>
              getLiteralValue(newTau, clause[k]) == 1;
          }
        } else if (clauseIndex !in impactedClauses') {
          assert clause[k] != falseLiteral;
          if (clause[k] == trueLiteral) {
            assert getLiteralValue(oldTau, clause[k]) == 1;
          } else {
            var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 0 <==>
              getLiteralValue(newTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }
  lemma notDone_literalsToSet(i : int)
    requires valid();
    requires 0 <= i < |clauses|;
    requires falseLiteralsCount[i] < |clauses[i]|;
    requires trueLiteralsCount[i] == 0;
    requires validClause(clauses[i]);
    requires forall literal :: literal in clauses[i] ==> validLiteral(literal);
    ensures exists literal :: literal in clauses[i]
                        && truthAssignment[getVariableFromLiteral(literal)] == -1;
  {
    assert forall literal :: validLiteral(literal) ==>
      -1 <= getLiteralValue(truthAssignment[..], literal) <= 1;
    var clause := clauses[i];
    countTrueLiterals0_noLiteralsTrue(truthAssignment[..], clause);
    if forall literal :: literal in clause ==> getLiteralValue(truthAssignment[..], literal) == 0 {
      var k := |clause|-1;
      while (k > 0)
        invariant 0 <= k < |clause| == |clauses[i]|;
        invariant countFalseLiterals(truthAssignment[..], clause[k..]) == |clause| - k;
        decreases k;
      {
        assert getLiteralValue(truthAssignment[..], clause[k]) == 0;
        k := k - 1;
      }
      assert countFalseLiterals(truthAssignment[..], clause) == |clauses[i]|;
      assert false;
    }
  }
  lemma setVariable_unsetVariablesDecreasesWithOne(oldTau : seq<int>, newTau : seq<int>, variable : int)
    requires validVariablesCount();
    requires validVariable(variable);
    requires validValuesTruthAssignment(oldTau);
    requires validValuesTruthAssignment(newTau);
    requires |oldTau| == |newTau|;
    requires forall i :: 0 <= i < |oldTau| && i != variable ==>
                oldTau[i] == newTau[i];
    requires oldTau[variable] == -1;
    requires newTau[variable] in [0, 1];
    ensures countUnsetVariables(newTau) + 1 == countUnsetVariables(oldTau);
  {
    var k := |newTau|-1;
    while (k > 0)
      invariant 0 <= k < |newTau|;
      invariant variable < k < |newTau| ==> 
        countUnsetVariables(newTau[k..]) == countUnsetVariables(oldTau[k..]);
      invariant 0 <= k <= variable ==>
        countUnsetVariables(newTau[k..])+1 == countUnsetVariables(oldTau[k..]);
    {
      k := k - 1;
    }
  }
  predicate isVariableSet(truthAssignment : seq<int>, variable : int)
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(truthAssignment);
    requires validVariable(variable);
  {
    truthAssignment[variable] != -1
  }
}
module {:extern "FileInput"} FileInput {
    class {:extern "Reader"} Reader {
        static function method {:extern "getContent"} getContent() : array<char>
        static function method {:extern "getTimestamp"} getTimestamp() : int 
    }
}
include "data_structures.dfy"
include "utils.dfy"
include "concerns/seq-predicates.dfy"
class Formula extends DataStructures {
  constructor(
    variablesCount : int,
    clauses : seq<seq<int>>
  )
    requires 0 < variablesCount;
    requires |clauses| > 0;
    requires forall clause :: (clause in clauses) ==>
               forall literal :: (literal in clause) ==> (
                 (literal < 0 && 0 < -literal <= variablesCount) ||
                 (literal > 0 && 0 < literal <= variablesCount));
    requires forall clause :: (clause in clauses) ==>
              forall x, y :: 0 <= x < y < |clause| ==>
                clause[x] < clause[y];
    ensures valid();
    ensures stack.size == 0;
    ensures fresh(stack);
    ensures fresh(stack.stack);
    ensures fresh(truthAssignment);
    ensures fresh(trueLiteralsCount);
    ensures fresh(falseLiteralsCount);
    ensures fresh(positiveLiteralsToClauses);
    ensures fresh(negativeLiteralsToClauses);
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
    this.truthAssignment :=
      Utils.newInitializedSeq(variablesCount, -1);
    ghost var truthAssignment' := truthAssignment[..];
    this.trueLiteralsCount := new int[|this.clauses|];
    this.falseLiteralsCount := new int[|this.clauses|];
    positiveLiteralsToClauses := new seq<int>[variablesCount];
    negativeLiteralsToClauses := new seq<int>[variablesCount];
    assert this.clauses == clauses';
    assert validClauses();
    this.createTFLArrays();
    ghost var trueLiteralsCount' := trueLiteralsCount[..];
    ghost var falseLiteralsCount' := falseLiteralsCount[..];
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
    assert forall x :: 0 <= x < truthAssignment.Length ==> truthAssignment[x] == -1;
    assert forall x :: 0 <= x < stack.stack.Length ==> |stack.stack[x]| == 0;
    assert validTruthAssignment();
    assert truthAssignment[..] == truthAssignment';
    assert trueLiteralsCount[..] == trueLiteralsCount';
    assert falseLiteralsCount[..] == falseLiteralsCount';
    assert positiveLiteralsToClauses[..] == positiveLiteralsToClauses';
    assert negativeLiteralsToClauses[..] == negativeLiteralsToClauses';
  }
  method createTFLArrays()
    requires validReferences();
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();
    requires trueLiteralsCount.Length == |clauses|;
    requires falseLiteralsCount.Length == |clauses|;
    requires forall value :: 0 <= value < truthAssignment.Length ==>
                truthAssignment[value] == -1;
    modifies trueLiteralsCount, falseLiteralsCount;
    ensures validTrueLiteralsCount(truthAssignment[..]);
    ensures validFalseLiteralsCount(truthAssignment[..]);
  {
    var i : int := 0;
    while (i < |clauses|)
      invariant 0 <= i <= |clauses|;
      invariant forall j :: 0 <= j < i ==> trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j]);
      invariant forall j :: 0 <= j < i ==> falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j]);
      decreases |clauses| - i;
    {
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      trueLiteralsCount[i] := 0;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      falseLiteralsCount[i] := 0;
      i := i + 1;
    }
  }
  predicate isSatisfied(truthAssignment: seq<int>)
    reads this;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
      forall cI :: 0 <= cI < |clauses| ==>
        isClauseSatisfied(truthAssignment, cI)
  }
  predicate isExtendingTau(tau : seq<int>, tau' : seq<int>)
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validValuesTruthAssignment(tau');
  {
    forall i :: 0 <= i < |tau| && tau[i] != -1 ==>
            tau[i] == tau'[i]
  }
  predicate isTauComplete(tau : seq<int>)
    reads this;
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
  {
    forall i :: 0 <= i < |tau| ==> tau[i] != -1
  }
  function getExtendedCompleteTau(tau : seq<int>) : seq<int>
    reads this;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires isSatisfiableExtend(tau);
    ensures (
      var tau' := getExtendedCompleteTau(tau);
      validValuesTruthAssignment(tau')
        && isTauComplete(tau') 
        && isExtendingTau(tau, tau')
        && isSatisfied(tau')
    );
  {
    var tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau') 
        && isExtendingTau(tau, tau')
        && isSatisfied(tau');
    tau'
  }
  predicate isSatisfiableExtend(tau : seq<int>)
    reads this;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
  {
    exists tau' :: validValuesTruthAssignment(tau') 
                && isTauComplete(tau') 
                && isExtendingTau(tau, tau')
                && isSatisfied(tau')
  }
  lemma forVariableNotSatisfiableExtend_notSatisfiableExtend(
    tau : seq<int>,
    variable : int
  ) 
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires validVariable(variable);
    requires !isSatisfiableExtend(tau[variable := 0]);
    requires !isSatisfiableExtend(tau[variable := 1]);
    ensures !isSatisfiableExtend(tau);
  {
    if (isSatisfiableExtend(tau)) {
      ghost var tauT := getExtendedCompleteTau(tau);
      if (tauT[variable] == 0) {
        assert isExtendingTau(tau[variable := 0], tauT);
      } else if (tauT[variable] == 1) {
        assert isExtendingTau(tau[variable := 1], tauT);
      }
    }
  }
  lemma extensionSatisfiable_baseSatisfiable(
    tau : seq<int>,
    variable : int,
    value : int
  ) 
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires validVariable(variable);
    requires value in [0,1];
    requires tau[variable] == -1;
    requires isSatisfiableExtend(tau[variable := value]);
    ensures isSatisfiableExtend(tau);
  {
    ghost var tau' := tau[variable := value];
    assert isSatisfiableExtend(tau');
    ghost var tau'' := getExtendedCompleteTau(tau');
    assert isExtendingTau(tau, tau'');
  }
  function method isUnitClause(index : int) : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount,
          falseLiteralsCount;
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);
    requires 0 <= index < |clauses|;
  {
    trueLiteralsCount[index] == 0 &&
    |clauses[index]| - falseLiteralsCount[index] == 1
  }
  function method isEmptyClause(index : int) : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount,
          falseLiteralsCount;
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);
    requires 0 <= index < |clauses|;
  {
    |clauses[index]| == falseLiteralsCount[index]
  }
  method createPositiveLiteralsToClauses()
    requires validReferences();
    requires validVariablesCount();
    requires validClauses();
    requires positiveLiteralsToClauses.Length == variablesCount;
    modifies positiveLiteralsToClauses;
    ensures validPositiveLiteralsToClauses();
  {
    var variable := 0;
    while (variable < variablesCount)
      invariant 0 <= variable <= variablesCount;
      invariant forall v :: 0 <= v < variable ==>
        validPositiveLiteralToClause(v, positiveLiteralsToClauses[v]);
      decreases variablesCount - variable;
    {
      positiveLiteralsToClauses[variable] := [];
      var clauseIndex := 0;
      while (clauseIndex < |clauses|)
        invariant 0 <= clauseIndex <= |clauses|;
        invariant forall v :: 0 <= v < variable ==>
          validPositiveLiteralToClause(v, positiveLiteralsToClauses[v]);
        invariant SeqPredicates.valuesBoundedBy(positiveLiteralsToClauses[variable], 0, |clauses|);
        invariant |positiveLiteralsToClauses[variable]| > 0 ==>
                    positiveLiteralsToClauses[variable][|positiveLiteralsToClauses[variable]|-1] < clauseIndex;
        invariant SeqPredicates.orderedAsc(positiveLiteralsToClauses[variable]);
        invariant forall cI :: cI in positiveLiteralsToClauses[variable] ==>
                    variable+1 in clauses[cI];
        invariant forall cI :: 0 <= cI < clauseIndex ==>
                    cI !in positiveLiteralsToClauses[variable] ==>
                      variable+1 !in clauses[cI];
        decreases |clauses| - clauseIndex;
      {
        if (variable+1 in clauses[clauseIndex]) {
          positiveLiteralsToClauses[variable] :=
            positiveLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }
  method createNegativeLiteralsToClauses()
    requires validReferences();
    requires validVariablesCount();
    requires validClauses();
    requires negativeLiteralsToClauses.Length == variablesCount;
    modifies negativeLiteralsToClauses;
    ensures validNegativeLiteralsToClauses();
  {
    var variable := 0;
    while (variable < variablesCount)
      invariant 0 <= variable <= variablesCount;
      invariant forall v :: 0 <= v < variable ==>
                  validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v]);
      decreases variablesCount - variable;
    {
      negativeLiteralsToClauses[variable] := [];
      var clauseIndex := 0;
      while (clauseIndex < |clauses|)
        invariant 0 <= clauseIndex <= |clauses|;
        invariant forall v :: 0 <= v < variable ==>
                  validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v]);
        invariant SeqPredicates.valuesBoundedBy(negativeLiteralsToClauses[variable], 0, |clauses|);
        invariant |negativeLiteralsToClauses[variable]| > 0 ==>
                    negativeLiteralsToClauses[variable][|negativeLiteralsToClauses[variable]|-1] < clauseIndex;
        invariant SeqPredicates.orderedAsc(negativeLiteralsToClauses[variable]);
        invariant forall cI :: cI in negativeLiteralsToClauses[variable] ==>
                    -variable-1 in clauses[cI];
        invariant forall cI :: 0 <= cI < clauseIndex ==>
                    cI !in negativeLiteralsToClauses[variable] ==>
                      -variable-1 !in clauses[cI];
        decreases |clauses| - clauseIndex;
      {
        if (-variable-1 in clauses[clauseIndex]) {
          negativeLiteralsToClauses[variable] :=
            negativeLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }
  method newLayerOnStack() 
    requires valid();
    requires 0 <= stack.size < stack.stack.Length;
    requires stack.size > 0 ==> |stack.stack[stack.size-1]| > 0;
    modifies stack;
    ensures valid();
    ensures stack.size == old(stack.size) + 1;
    ensures 0 < stack.size <= stack.stack.Length;
    ensures stack.stack == old(stack.stack);
    ensures forall i :: 0 <= i < stack.stack.Length ==>
      stack.stack[i] == old(stack.stack[i]);
    ensures stack.contents == old(stack.contents);
  {
    stack.createNewLayer();
    assert stack.contents == old(stack.contents);
    assert old(truthAssignment[..]) == truthAssignment[..];
  }
  method undoLayerOnStack() 
    requires valid();
    requires 0 < stack.size <= stack.stack.Length;
    requires |stack.stack[stack.size-1]| > 0;
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount,
             falseLiteralsCount;
    ensures valid();
    ensures stack.size == old(stack.size) - 1;
    ensures stack.stack == old(stack.stack);
    ensures 0 <= stack.size < stack.stack.Length;
    ensures forall i :: 0 <= i < stack.stack.Length && i != stack.size ==>
      stack.stack[i] == old(stack.stack[i]);
    ensures |stack.stack[stack.size]| == 0;
    ensures forall x :: x in old(stack.contents)
      && x !in old(stack.stack[stack.size-1])
      ==> x in stack.contents;
    ensures forall x :: x in old(stack.stack[stack.size-1]) ==>
            x !in stack.contents;
    ensures stack.contents == old(stack.contents) - old(stack.getLastLayer());
    ensures stack.size > 0 ==> 
              |stack.stack[stack.size-1]| > 0;
  {
    var k := 0;
    var layer := stack.stack[stack.size-1];
    stack.stack[stack.size-1] := [];
    stack.size := stack.size - 1;
    while (k < |layer|) 
      modifies stack, truthAssignment, trueLiteralsCount, 
               falseLiteralsCount;
      invariant 0 <= k <= |layer|;
      invariant forall k' :: 0 <= k' < k ==> layer[k'] !in stack.contents;
      invariant forall k' :: k <= k' < |layer| ==> layer[k'] in stack.contents;
      invariant 0 <= stack.size < stack.stack.Length;
      invariant old(stack.variablesCount) == stack.variablesCount;
      invariant old(stack.size)-1 == stack.size;
      invariant old(stack.stack) == stack.stack;
      invariant forall i :: 0 <= i < stack.size ==> 
        old(stack.stack[i]) == stack.stack[i];
      invariant forall i :: 0 <= i < stack.size ==> 
        forall j :: j in stack.stack[i] ==>
          j in stack.contents;
      invariant forall j :: j in stack.contents ==> 
        j in old(stack.contents);
      invariant k > 0 ==> 
        stack.contents == old(stack.contents) - set j | j in layer[..k];
      invariant forall i :: stack.size <= i < stack.stack.Length ==> 
        stack.stack[i] == [];
      invariant (forall j :: 0 <= j < truthAssignment.Length && truthAssignment[j] != -1 ==>
        (j, convertIntToBool(truthAssignment[j])) in stack.contents);
      invariant forall j :: 0 <= j < k ==>
        truthAssignment[layer[j].0] == -1;
      invariant forall j :: 0 <= j < truthAssignment.Length && truthAssignment[j] == -1 ==>
        (j, false) !in stack.contents && (j, true) !in stack.contents;
      invariant truthAssignment.Length == variablesCount;
      invariant forall i :: 0 <= i < truthAssignment.Length ==>
        -1 <= truthAssignment[i] <= 1;
      invariant forall cI :: 0 <= cI < |clauses| ==>
        trueLiteralsCount[cI] == countTrueLiterals(truthAssignment[..], clauses[cI]);
      invariant forall cI :: 0 <= cI < |clauses| ==>
        falseLiteralsCount[cI] == countFalseLiterals(truthAssignment[..], clauses[cI]);
      decreases |layer| - k;
    {
      var x := layer[k];
      k := k + 1;
      var (variable, value) := x;
      ghost var previousTau := truthAssignment[..];
      truthAssignment[variable] := -1;
      ghost var newTau := truthAssignment[..];
      assert validValuesTruthAssignment(newTau);
      assert forall i :: 0 <= i < |previousTau| && i != variable
        ==> previousTau[i] == newTau[i];
      assert previousTau[variable] in {0,1} && newTau[variable] == -1;
      stack.contents := stack.contents - {x};
      var positivelyImpactedClauses := positiveLiteralsToClauses[variable]; // decrease true counter
      var negativelyImpactedClauses := negativeLiteralsToClauses[variable];  // decrease false counters
      if (!value) {
        negativelyImpactedClauses := positiveLiteralsToClauses[variable]; // decrease true counter
        positivelyImpactedClauses := negativeLiteralsToClauses[variable];  // decrease false counters
      }
      assert SeqPredicates.valuesBoundedBy(positivelyImpactedClauses, 0, |clauses|);
      assert SeqPredicates.valuesBoundedBy(negativelyImpactedClauses, 0, |clauses|);
      undoImpactedClauses_TFSArraysModified(
        previousTau,
        newTau,
        variable,
        positivelyImpactedClauses,
        negativelyImpactedClauses
      );
      var i := 0;
      while (i < |positivelyImpactedClauses|)
        modifies trueLiteralsCount;
        invariant 0 <= i <= |positivelyImpactedClauses|;
        invariant forall i' :: 0 <= i' < |clauses| && i' !in positivelyImpactedClauses ==>
          trueLiteralsCount[i']
            == countTrueLiterals(newTau, clauses[i']);
        invariant forall i' :: 0 <= i' < i ==>
          trueLiteralsCount[positivelyImpactedClauses[i']]
            == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']]);
        invariant forall i' :: i <= i' < |positivelyImpactedClauses| ==>
          trueLiteralsCount[positivelyImpactedClauses[i']]
            == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']]);
      {
        var clauseIndex := positivelyImpactedClauses[i];
        var clause := clauses[clauseIndex];
        assert validClause(clause);
        unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
        trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;
        i := i + 1;
      }
      i := 0;
      while (i < |negativelyImpactedClauses|)
        modifies falseLiteralsCount;
        invariant 0 <= i <= |negativelyImpactedClauses|;
        invariant forall i' :: 0 <= i' < i ==>
          falseLiteralsCount[negativelyImpactedClauses[i']]
            == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']]);
        invariant forall i' :: i <= i' < |negativelyImpactedClauses| ==>
          falseLiteralsCount[negativelyImpactedClauses[i']]
            == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']]);
        invariant forall i' :: 0 <= i' < |clauses| && i' !in negativelyImpactedClauses ==>
          falseLiteralsCount[i']
            == countFalseLiterals(newTau, clauses[i']);
        decreases |negativelyImpactedClauses| - i;
      {
        var clauseIndex := negativelyImpactedClauses[i];
        unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
        falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
        i := i + 1;
      }
    }
  }
  method setVariable(variable : int, value : bool) 
    requires valid();
    requires validVariable(variable);
    requires truthAssignment[variable] == -1;
    requires 0 < stack.size <= stack.stack.Length;
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount, 
             falseLiteralsCount;
    ensures valid();
    ensures value == false ==> truthAssignment[variable] == 0;
    ensures value == true ==> truthAssignment[variable] == 1;
    ensures value == false ==> old(truthAssignment[..][variable := 0]) 
      == truthAssignment[..];
    ensures value == true ==> old(truthAssignment[..][variable := 1]) 
      == truthAssignment[..];
    ensures stack.size == old(stack.size);
    ensures stack.stack == old(stack.stack);
    ensures 0 < stack.size <= stack.stack.Length;
    ensures |stack.stack[stack.size-1]| == |old(stack.stack[stack.size-1])| + 1;
    ensures stack.contents == old(stack.contents) + {(variable, value)};
    ensures forall i :: 0 <= i < stack.size-1 ==> 
      stack.stack[i] == old(stack.stack[i]);
    ensures countUnsetVariables(truthAssignment[..]) + 1 == 
      old(countUnsetVariables(truthAssignment[..]));
  {
    ghost var oldTau := truthAssignment[..];
    var el := (variable, value);
    var iL := stack.size - 1; // index layer
    stack.variableNotInContents_variableNotInStack(variable);
    stack.stack[iL] := stack.stack[iL] + [el];
    stack.contents := stack.contents + {el};
    if (value) {
      truthAssignment[variable] := 1;
    } else {
      truthAssignment[variable] := 0;
    }
    ghost var newTau := truthAssignment[..];
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
    ghost var elI := |stack.stack[iL]|-1;
    assert stack.contents - old(stack.contents) == {el};
    assert forall i :: 0 <= i < iL ==>
      old(stack.stack[i]) == stack.stack[i];
    assert old(stack.stack[iL]) == stack.stack[iL][..elI];
    assert stack.stack[iL][|stack.stack[iL]| - 1] == el;
    assert validStack();
    var trueLiteral := variable+1;
    var falseLiteral := -variable-1;
    if (!value) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    var i := 0;
    var impactedClauses := positiveLiteralsToClauses[variable];
    var impactedClauses' := negativeLiteralsToClauses[variable];
    if (!value) {
      impactedClauses := negativeLiteralsToClauses[variable];
      impactedClauses' := positiveLiteralsToClauses[variable];
    }
    clausesNotImpacted_TFArraysSame(
      oldTau, 
      newTau, 
      variable, 
      impactedClauses, 
      impactedClauses'
    );
    Utils.prop_seq_predicate(|clauses|, impactedClauses);
    assert value ==> validPositiveLiteralToClause(variable, impactedClauses);
    assert !value ==> validNegativeLiteralsToClause(variable, impactedClauses);
    while (i < |impactedClauses|)
      modifies trueLiteralsCount;
      invariant 0 <= i <= |impactedClauses|;
      invariant forall j :: 0 <= j < |clauses| && j !in impactedClauses
        ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j]);
      invariant forall j :: 0 <= j < i ==>
        trueLiteralsCount[impactedClauses[j]] 
          == countTrueLiterals(newTau, clauses[impactedClauses[j]]);
      invariant forall j :: i <= j < |impactedClauses| ==>
        trueLiteralsCount[impactedClauses[j]]
          == countTrueLiterals(oldTau, clauses[impactedClauses[j]]);
      decreases |impactedClauses| - i;
    {
      var clauseIndex := impactedClauses[i];
      setVariable_countTrueLiteralsIncreasesWithOne(
        oldTau, 
        newTau, 
        variable, 
        clauses[clauseIndex]
      );
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;
      assert trueLiteral in clauses[clauseIndex]
        && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);
      i := i + 1;
    }
    assert validTrueLiteralsCount(newTau);
    var i' := 0;
    Utils.prop_seq_predicate(|clauses|, impactedClauses');
    assert value ==> validNegativeLiteralsToClause(variable, impactedClauses');
    assert !value ==> validPositiveLiteralToClause(variable, impactedClauses');
    while (i' < |impactedClauses'|)
      modifies falseLiteralsCount;
      invariant 0 <= i' <= |impactedClauses'|;
      invariant forall j :: 0 <= j < |clauses| && j !in impactedClauses'
        ==> falseLiteralsCount[j] == countFalseLiterals(newTau, clauses[j]);
      invariant forall j :: 0 <= j < i' ==>
        falseLiteralsCount[impactedClauses'[j]] ==
          countFalseLiterals(newTau, clauses[impactedClauses'[j]]);
      invariant forall j :: i' <= j < |impactedClauses'| ==>
        falseLiteralsCount[impactedClauses'[j]] ==
          countFalseLiterals(oldTau, clauses[impactedClauses'[j]]);
      decreases |impactedClauses'| - i';
    {
      var clauseIndex := impactedClauses'[i'];
      setVariable_countFalseLiteralsIncreasesWithOne(
        oldTau, 
        newTau, 
        variable, 
        clauses[clauseIndex]
      );
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;
      i' := i' + 1;
    }
    assert validReferences();
    assert validVariablesCount();
    assert validClauses();
    assert validStack();
    assert validTruthAssignment();
    assert validTrueLiteralsCount(truthAssignment[..]);
    assert validFalseLiteralsCount(truthAssignment[..]);
    assert validPositiveLiteralsToClauses();
    assert validNegativeLiteralsToClauses();
  }
  function method hasEmptyClause() : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, 
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    ensures hasEmptyClause() == true ==> 
      exists i :: 0 <= i < |clauses| 
               && falseLiteralsCount[i] == |clauses[i]|;
    ensures hasEmptyClause() == false ==>
      forall i :: 0 <= i < |clauses| ==>
        falseLiteralsCount[i] < |clauses[i]|;
  {
    if i : int :| 0 <= i < |clauses| && falseLiteralsCount[i] == |clauses[i]|
      then true
      else false
  }
  function method isEmpty() : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, 
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    requires !hasEmptyClause();
    ensures isEmpty() == true ==> 
      forall i :: 0 <= i < |clauses| ==>
        trueLiteralsCount[i] > 0;
    ensures isEmpty() == false ==>
      exists i :: 0 <= i < |clauses| 
               && trueLiteralsCount[i] == 0;
  {
    if i : int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0 
      then false
      else true
  }
  lemma notEmptyNoEmptyClauses_stackNotFull()
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();
    requires stack.size > 0 ==> 
              |stack.stack[stack.size-1]| > 0;
    ensures stack.size < stack.stack.Length;
  {
    if (stack.size == stack.stack.Length) {
      stack.ifFull_containsAllVariables();
      forall v | 0 <= v < stack.size
        ensures truthAssignment[v] != -1;
      {
        if (truthAssignment[v] == -1) {
          assert (v, true) !in stack.contents;
          assert (v, false) !in stack.contents;
          assert stack.occursInContents(v);
          var x :| x in stack.contents && x.0 == v;
          var (i, b) := x;
          assert x == (v, true) || x == (v, false);
          assert false;
        }
      }
      allVariablesSet_done();
      assert false;
    }
  }
  lemma allVariablesSet_done()
    requires valid();
    requires forall v :: validVariable(v) ==> 
      isVariableSet(truthAssignment[..], v);
    ensures hasEmptyClause() || isEmpty();
  {
    if (!hasEmptyClause()) {
      if (!isEmpty()) {
        var k := 0;
        assert forall k :: 0 <= k < |clauses| ==>
          falseLiteralsCount[k] < |clauses[k]|;
        while (k < |clauses|)
          invariant 0 <= k <= |clauses|;
          invariant forall k' :: 0 <= k' < k ==>
                      trueLiteralsCount[k'] > 0;
          decreases |clauses| - k;
        {
          assert validClause(clauses[k]);
          assert falseLiteralsCount[k] < |clauses[k]|;
          assert forall x :: x in clauses[k] ==>
            isVariableSet(truthAssignment[..], getVariableFromLiteral(x));
          tauFullClauseNotEmpty_clauseIsSatisfied(k);
          k := k + 1;
        }
      } else {
      }
    } else {
    }
  }
  lemma tauFullClauseNotEmpty_clauseIsSatisfied(cI : int)
    requires valid();
    requires 0 <= cI < |clauses|;
    requires validClause(clauses[cI]);
    requires forall x :: x in clauses[cI] ==>
      isVariableSet(truthAssignment[..], getVariableFromLiteral(x));
    requires falseLiteralsCount[cI] < |clauses[cI]|;
    ensures trueLiteralsCount[cI] > 0;
  {
    var tau := truthAssignment[..];
    var clause := clauses[cI];
    assert forall x :: x in clause ==>
      getLiteralValue(tau, x) in [0, 1];
    if forall x :: x in clause ==> getLiteralValue(tau, x) == 0 {
      var k := |clause| - 1;
      while (k > 0)
        invariant 0 <= k <= |clause|;
        invariant countFalseLiterals(tau, clause[k..]) == |clause| - k;
        decreases k;
      {
        k := k - 1;
      }
      assert countFalseLiterals(tau, clause) == |clause| == |clauses[cI]|;
    } else {
      assert exists x :: x in clause && getLiteralValue(tau, x) == 1;
      existsTrueLiteral_countTrueLiteralsPositive(clause, tau);
    }
  }
  lemma existsTrueLiteral_countTrueLiteralsPositive(clause : seq<int>, truthAssignment : seq<int>)
    requires valid();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires exists x :: x in clause && getLiteralValue(truthAssignment, x) == 1;
    ensures countTrueLiterals(truthAssignment, clause) > 0;
  {
    if (|clause| == 0) {}
    else if (getLiteralValue(truthAssignment, clause[0]) == 1) {}
    else {
      existsTrueLiteral_countTrueLiteralsPositive(clause[1..], truthAssignment);
    }
  }
  method chooseLiteral() returns (x : int)
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();
    ensures valid();
    ensures validLiteral(x);
    ensures truthAssignment[getVariableFromLiteral(x)] == -1;
    ensures getLiteralValue(truthAssignment[..], x) == -1;
  {
    var i : int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0; 
    assert validClause(clauses[i]);
    notDone_literalsToSet(i);
    var literal :| literal in clauses[i] 
            && truthAssignment[getVariableFromLiteral(literal)] == -1;
    return literal;
  }
  method setLiteral(literal : int, value : bool)
    requires valid();
    requires validLiteral(literal);
    requires getLiteralValue(truthAssignment[..], literal) == -1;
    requires 0 < stack.size <= stack.stack.Length;
    modifies truthAssignment, stack, stack.stack, trueLiteralsCount, 
             falseLiteralsCount;
    ensures valid();
    ensures 0 < stack.size <= stack.stack.Length;
    ensures stack.size == old(stack.size);
    ensures stack.stack == old(stack.stack);
    ensures |stack.stack[stack.size-1]| > 0;
    ensures forall i :: 0 <= i < stack.stack.Length && i != stack.size-1 ==> 
      stack.stack[i] == old(stack.stack[i]);
    ensures forall x :: x in old(stack.contents) ==> 
                x in stack.contents;
    ensures stack.contents == old(stack.contents) + stack.getLastLayer();
    ensures countUnsetVariables(truthAssignment[..]) < 
      old(countUnsetVariables(truthAssignment[..]));
    ensures (
      ghost var tau := old(truthAssignment[..]);
      ghost var (variable, val) := convertLVtoVI(literal, value);
      ghost var tau' := tau[variable := val];
      isSatisfiableExtend(tau') <==>
              isSatisfiableExtend(truthAssignment[..])
    );
    decreases countUnsetVariables(truthAssignment[..]);
  {
    ghost var tau := truthAssignment[..];
    ghost var (vari, val) := convertLVtoVI(literal, value);
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
    while (k < |negativelyImpactedClauses|) 
      invariant 0 <= k <= |negativelyImpactedClauses|;
      invariant valid();
      invariant 0 < stack.size <= stack.stack.Length;
      invariant stack.size == old(stack.size);
      invariant stack.stack == old(stack.stack);
      invariant |stack.stack[stack.size-1]| > 0;
      invariant forall i :: 0 <= i < stack.size-1 ==> 
        stack.stack[i] == old(stack.stack[i]);
      invariant forall x :: x in old(stack.contents) ==> x in stack.contents;
      invariant unsetVariablesCount == countUnsetVariables(truthAssignment[..]);
      invariant unsetVariablesCount < 
                          old(countUnsetVariables(truthAssignment[..]));
      invariant isSatisfiableExtend(tau') <==>
                    isSatisfiableExtend(truthAssignment[..]);
      decreases |negativelyImpactedClauses| - k;
    {
      var clauseIndex := negativelyImpactedClauses[k];
      var clause := clauses[clauseIndex];
      assert validClause(clause);
      if (trueLiteralsCount[clauseIndex] == 0 &&
        falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|) {
        unitClause_existsUnsetLiteral(clauseIndex);
        var literal :| literal in clause 
                        && truthAssignment[getVariableFromLiteral(literal)] == -1;
        ghost var (v', val') := convertLVtoVI(literal, true);
        ghost var tau'' := truthAssignment[..];
        unitClauseLiteralFalse_tauNotSatisfiable(tau'', clauseIndex, literal);
        setLiteral(literal, true);
        assert isSatisfiableExtend(tau''[v' := val']) <==>
                isSatisfiableExtend(truthAssignment[..]);
        if (isSatisfiableExtend(truthAssignment[..])) {
          extensionSatisfiable_baseSatisfiable(tau'', v', val');
        } else {
          forVariableNotSatisfiableExtend_notSatisfiableExtend(tau'', v');
        }
        assert !isSatisfiableExtend(tau'') <==>
                  !isSatisfiableExtend(truthAssignment[..]);
        unsetVariablesCount := countUnsetVariables(truthAssignment[..]);
        assert unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]));
      }
      k := k + 1;
    }
    assert unsetVariablesCount == countUnsetVariables(truthAssignment[..]);
    assert unsetVariablesCount < old(countUnsetVariables(truthAssignment[..]));
  }
  lemma unitClause_existsUnsetLiteral(clauseIndex : int)
    requires valid();
    requires 0 <= clauseIndex < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires trueLiteralsCount[clauseIndex] == 0;
    requires falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|;
    ensures exists literal :: literal in clauses[clauseIndex]
                && truthAssignment[getVariableFromLiteral(literal)] == -1;
  {
    ghost var tau := truthAssignment[..];
    var clause := clauses[clauseIndex];
    countTrueLiterals0_noLiteralsTrue(tau, clause);
    var k := |clause| - 1;
    var flc := 0;
    var ok := false;
    var index := 0;
    while (k >= 0) 
      invariant -1 <= k < |clause|;
      invariant forall k' :: k < k' < |clause| ==> 
        getLiteralValue(tau, clause[k']) != 1;
      invariant k >=0 ==> countTrueLiterals(tau, clause[k..]) == 0;
      invariant countFalseLiterals(tau, clause[k+1..]) == flc;
      invariant flc < |clause|;
      invariant flc == |clause|-k-1 ==> ok == false;
      invariant flc < |clause|-k-1 ==> ok == true;
      invariant ok ==> 0 <= index < |clause|;
      invariant ok ==> getLiteralValue(tau, clause[index]) == -1;
      decreases k;
    {
      if (getLiteralValue(tau, clause[k]) == 0) {
        flc := flc + 1;
      }
      if (getLiteralValue(tau, clause[k]) == -1) {
        ok := true;
        index := k;
      }
      k := k - 1;
    }
    assert ok;
    assert clause[index] in clauses[clauseIndex];
  }
  method render(truthAssignment : seq<int>) 
    requires valid();
    requires validValuesTruthAssignment(truthAssignment);
    requires |truthAssignment| == variablesCount;
  {
    var clauseIndex := 0;
    print "Solution:\n", truthAssignment, "\n\nClauses:\n";
    while (clauseIndex < |clauses|) 
        invariant 0 <= clauseIndex <= |clauses|;
        decreases |clauses| - clauseIndex;
    {
        var clause := clauses[clauseIndex];
        assert validClause(clause);
        var literalIndex := 0;
        while (literalIndex < |clause|) 
            decreases |clause| - literalIndex;
        {
            var literal := clause[literalIndex];
            assert validLiteral(literal);
            print literal;
            assert 0 <= Utils.abs(literal)-1 < variablesCount;
            if (literal < 0 && truthAssignment[-literal-1] == 0) {
              print '*';
            } else if (literal > 0 && truthAssignment[literal-1] == 1) {
              print '*';
            }
            print ' ';
            literalIndex := literalIndex + 1;
        }
        print '\n';
        clauseIndex := clauseIndex+1;
    }
  }
  lemma hasEmptyClause_notSatisfiable()
    requires valid();
    requires hasEmptyClause();
    ensures !isSatisfiableExtend(truthAssignment[..]);
  {
    var tau := truthAssignment[..];
    var clauseIndex :| 0 <= clauseIndex < |clauses|
               && falseLiteralsCount[clauseIndex] == |clauses[clauseIndex]|;
    var clause := clauses[clauseIndex];
    assert validClause(clause);
    allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex);
    if tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau') 
        && isExtendingTau(tau, tau')
        && isSatisfied(tau') {
      assert forall l :: l in clause ==>
        getLiteralValue(tau, l) == getLiteralValue(tau', l) == 0;
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }
  lemma allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex : int) 
    requires valid();
    requires 0 <= clauseIndex < |clauses|;
    requires falseLiteralsCount[clauseIndex] == |clauses[clauseIndex]|;
    requires validClause(clauses[clauseIndex]);
    ensures forall literal :: literal in clauses[clauseIndex] ==>
              getLiteralValue(truthAssignment[..], literal) == 0;
  {
    var clause := clauses[clauseIndex];
    var k := 0;
    var flc := 0;
    var tau := truthAssignment[..];
    while (k < |clause|)
      invariant 0 <= k <= |clause|;
      invariant countFalseLiterals(tau, clause[k..]) ==
                  falseLiteralsCount[clauseIndex] - k;
      invariant forall k' :: 0 <= k' < k ==>
        getLiteralValue(tau, clause[k']) == 0;
      decreases |clause| - k;
    {
      k := k + 1;
    }
  }
  lemma isEmpty_sastisfied()
    requires valid();
    requires !hasEmptyClause();
    requires isEmpty();
    ensures isSatisfiableExtend(truthAssignment[..]);
  {
    assert forall i :: 0 <= i < |clauses| ==>
        trueLiteralsCount[i] > 0;
    forall i | 0 <= i < |clauses| 
      ensures isClauseSatisfied(truthAssignment[..], i);
    {
      countTrueLiteralsX_existsTrueLiteral(truthAssignment[..], clauses[i]);
    }
    assert isSatisfied(truthAssignment[..]);
    assert variablesCount > 0;
    partialTauSatisfied_isSatisfiableExtend(truthAssignment[..]);
  }
  lemma partialTauSatisfied_isSatisfiableExtend(tau : seq<int>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validClauses();
    requires isSatisfied(tau);
    ensures isSatisfiableExtend(tau);
    decreases countUnsetVariables(tau);
  {
    if (isTauComplete(tau)) {
    } else {
      var x :| 0 <= x < |tau| && tau[x] == -1;
      var tau' := tau[x := 0];
      forall i | 0 <= i < |clauses|
        ensures isClauseSatisfied(tau', i);
      {
        assert isClauseSatisfied(tau, i);
      }
      assert isSatisfied(tau');
      var k := |tau'|-1;
      while (k > 0)
        invariant 0 <= k < |tau'|;
        invariant x < k < |tau'| ==> 
          countUnsetVariables(tau'[k..]) == countUnsetVariables(tau[k..]);
        invariant 0 <= k <= x ==>
          countUnsetVariables(tau'[k..])+1 == countUnsetVariables(tau[k..]);
      {
        k := k - 1;
      }
      assert countUnsetVariables(tau) - 1 == countUnsetVariables(tau');
      partialTauSatisfied_isSatisfiableExtend(tau');
    }
  }
  lemma unitClause_allFalseExceptLiteral(
    truthAssignment : seq<int>,
    clauseIndex : int,
    literal : int
  ) 
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires validTrueLiteralsCount(truthAssignment);
    requires validFalseLiteralsCount(truthAssignment);
    requires 0 <= clauseIndex < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires validLiteral(literal);
    requires falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|;
    requires literal in clauses[clauseIndex];
    requires getLiteralValue(truthAssignment, literal) == -1;
    requires forall literal :: literal in clauses[clauseIndex] ==> 
              getLiteralValue(truthAssignment, literal) != 1;
    ensures forall literal' :: literal' in clauses[clauseIndex] && literal' != literal ==>
            getLiteralValue(truthAssignment, literal') != -1;
  {
    var clause := clauses[clauseIndex];
    var literalIndex :| 0 <= literalIndex < |clause| && clause[literalIndex] == literal;
    if i :| 0 <= i < |clause| 
        && i != literalIndex 
        && getLiteralValue(truthAssignment, clause[i]) == -1 {
        var a := i;
        var b := literalIndex;
        if (b < a) {
          a := literalIndex;
          b := i;
        }
        assert a < b;
        assert getLiteralValue(truthAssignment, clause[a]) == -1;
        assert getLiteralValue(truthAssignment, clause[b]) == -1;
        var k := |clause|-1;
        while (k >= 0)
          invariant -1 <= k < |clause|;
          invariant 0 <= a < b < |clause|;
          invariant b <= k ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) <= |clause|-(k+1);
          invariant a <= k < b  ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) <= |clause|-(k+1)-1;
          invariant k < a  ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) <= |clause|-(k+1)-2;
          decreases k;
        {
          k := k-1;
        }
        assert false;
    }
  }
  lemma unitClauseLiteralFalse_tauNotSatisfiable(
    truthAssignment : seq<int>,
    clauseIndex : int,
    literal : int
  ) 
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires validTrueLiteralsCount(truthAssignment);
    requires validFalseLiteralsCount(truthAssignment);
    requires 0 <= clauseIndex < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires validLiteral(literal);
    requires trueLiteralsCount[clauseIndex] == 0;
    requires falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|;
    requires truthAssignment[getVariableFromLiteral(literal)] == -1;
    requires literal in clauses[clauseIndex];
    ensures (
      ghost var (variable, value) := convertLVtoVI(literal, false);
      !isSatisfiableExtend(truthAssignment[variable := value])
    );
  {
    var clause := clauses[clauseIndex];
    var (variable, value) := convertLVtoVI(literal, false);
    countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);
    unitClause_allFalseExceptLiteral(truthAssignment, clauseIndex, literal);
    var tau := truthAssignment[variable := value];
    var k := |clause| - 1;
    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall k' :: k < k' < |clause| ==>
        getLiteralValue(tau, clause[k']) == 0;
      decreases k;
    {
      if (getLiteralValue(tau, clause[k]) == 1) {
        assert literal in clause;
        assert clause[k] in clause;
        if (literal == clause[k]) {
          assert getLiteralValue(truthAssignment, literal) == -1;
          assert getLiteralValue(tau, literal) == 0;
          assert false;
        } else if (-literal == clause[k]) {
          assert false;
        } else {
          assert getLiteralValue(truthAssignment, clause[k]) != 1;
          assert getVariableFromLiteral(clause[k]) != variable;
          assert tau[getVariableFromLiteral(clause[k])]
              == truthAssignment[getVariableFromLiteral(clause[k])];
          assert getLiteralValue(tau, clause[k]) != 1;
          assert false;
        }
        assert false;
      }
      if (getLiteralValue(tau, clause[k]) == -1) {
        assert false;
      }
      k := k - 1;
    }
    if tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau')
        && isExtendingTau(tau, tau')
        && isSatisfied(tau') {
      assert forall l :: l in clause ==>
        getLiteralValue(tau, l) == getLiteralValue(tau', l) == 0;
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }
}
include "parser.dfy"
include "file_input.dfy"
include "my_datatypes.dfy"
module Input {
    import Parser
    import FileInput
    import opened MyDatatypes
    function method getInput() : Maybe<(int, seq<seq<int>>)> 
        reads *;
    {
        Parser.parseContent(
            FileInput.Reader.getContent()[0..])
    }
    function method getTimestamp() : int
    {
      FileInput.Reader.getTimestamp()
    }
}
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
module MyDatatypes {
    datatype Maybe<T> = Error(string) | Just(value : T)
}include "my_datatypes.dfy"
module Parser {
    import opened MyDatatypes
    function method skipLine(content : string) : string 
        decreases |content|;
        ensures |content| > 0 ==> |skipLine(content)| < |content|;
    {
        if |content| == 0 then content
        else
            if content[0] == '\n' then content[1..] 
            else skipLine(content[1..])
    }
    lemma prop_skipWhiteSpaces(content : string)
        ensures |skipWhiteSpaces(content)| <= |content|;
    {}
    function method skipWhiteSpaces(content : string) : string 
        decreases |content|;
    {
        if |content| == 0 then content
        else
            if content[0] == ' ' then skipWhiteSpaces(content[1..])
            else if content[0] == '\n' then skipWhiteSpaces(content[1..])
            else content
    }
    function method isDigit(chr : char) : bool
    {
        '0' <= chr <= '9'
    }
    function method toInt(chr: char) : int
        requires isDigit(chr)
    {
        (chr as int) - ('0' as int)
    }
    lemma prop_extractDigits(content : string) 
        ensures |content| == |extractDigits(content).0| + |extractDigits(content).1|;
    {}
    function method extractDigits(content : string) : (seq<int>, string)
        decreases |content|;
    {
        if (|content| == 0) then ([], content)
        else if (isDigit(content[0])) then
            var (h, tail) := extractDigits(content[1..]);
            ([toInt(content[0])] + h, tail)
        else ([], content)
    }
    function method joinInts(number : int, ints : seq<int>) : int 
        decreases |ints|;
    {
        if |ints| == 0 then number
        else joinInts(number * 10 + ints[0], ints[1..])
    }
    lemma prop_getNextNumber(content : string)
        requires getNextNumber(content).Just?;
        ensures |getNextNumber(content).value.1| < |content|;
    {
        prop_extractDigits(content[1..]);
        assert content[0] == '-' ==> 
            |getNextNumber(content[1..]).value.1| == |extractDigits(content[1..]).1| < |content[1..]| < |content|;
        prop_extractDigits(content);
        assert content[0] != '-' ==> 
            |getNextNumber(content).value.1| == |extractDigits(content).1| < |content|;
    }
    function method getNextNumber(content : string) : Maybe<(int, string)>
        decreases |content|;
    {
        if (|content| == 0) then Error("content finished unexpectatly")
        else if (content[0] == '-') then
            var (digits, newContent) := extractDigits(content[1..]);
            prop_extractDigits(content[1..]);
            if |digits| == 0 then Error("only alpha characters ahead, no numbers after -")
            else
                var number := joinInts(0, digits);
                assert |newContent| < |content|;
                Just((-number, newContent))
        else
            var (digits, newContent) := extractDigits(content);
            prop_extractDigits(content);
            if |digits| == 0 then Error("only alpha characters ahead, no numbers")
            else 
                var number := joinInts(0, digits);
                assert |newContent| < |content|;
                Just((number, newContent))
    }
    function method extractNumbers(content : string) : (seq<int>, string)
        decreases |content|;
    {
        prop_skipWhiteSpaces(content);
        var content' := skipWhiteSpaces(content);
        match getNextNumber(content')
            case Error(_) => ([], content')
            case Just((number, content'')) =>
                prop_getNextNumber(content');
                prop_skipWhiteSpaces(content'');
                var content''' := skipWhiteSpaces(content'');
                assert |content'''| < |content'| <= |content|;
                var (fst, snd) := extractNumbers(content''');
                ([number] + fst, snd)
    }
    function method getNextClause(numbers : seq<int>) : Maybe<(seq<int>, seq<int>)>
        decreases |numbers|;
    {
        if (|numbers| == 0) then Error("no 0 there")
        else 
            if (numbers[0] == 0) then Just(([], numbers[1..]))
            else
                var head := [numbers[0]];
                match getNextClause(numbers[1..])
                    case Error(m) => Error(m)
                    case Just((tail, numbers)) => 
                        Just((head + tail, numbers))
    }
    function method getClauses(clausesCount : int, numbers : seq<int>) :
        Maybe<(seq<seq<int>>, seq<int>)>
        decreases clausesCount, |numbers|;
    {
        if (clausesCount <= 0 || |numbers| == 0) then Just(([], numbers))
        else 
            match getNextClause(numbers)
                case Error(m) => Error(m)
                case Just((clause, numbers)) =>
                    match getClauses(clausesCount - 1, numbers)
                        case Error(m) => Error(m)
                        case Just((clauses, numbers)) =>
                            Just(([clause] + clauses, numbers))
    }
    function method getToInput(content : string) : Maybe<string>
        decreases |content|;
    {
        prop_skipWhiteSpaces(content);
        var content := skipWhiteSpaces(content);
        if |content| == 0 then Error("nothing found")
        else if content[0] == 'c' then
            getToInput(skipLine(content))
        else if content[0] == 'p' then (
            var content := skipWhiteSpaces(content[1..]);
            if |content| < 3 then Error("input not correctly formated")
            else Just(skipWhiteSpaces(content[3..])))
        else Error("invalid symbol")
    }
    function method parseContent(content : string) :
        Maybe<(int, seq<seq<int>>)>
    {
        match getToInput(content)
            case Error(m) => Error(m)
            case Just(content) =>
                match getNextNumber(content)
                    case Error(m) => Error(m)
                    case Just((variablesCount, content)) =>
                        match getNextNumber(skipWhiteSpaces(content))
                            case Error(m) => Error(m)
                            case Just((clausesCount, content)) =>
                                var (numbers, _) := extractNumbers(content);
                                match getClauses(clausesCount, numbers)
                                    case Error(m) => Error(m)
                                    case Just((clauses, content)) =>
                                        Just((variablesCount, clauses))
    }
}module SeqPredicates {
  predicate valueBoundedBy(value : int, min : int, max : int) {
    min <= value < max
  }
  predicate valuesBoundedBy(s: seq<int>, min : int, max: int) {
    (forall el :: el in s ==>
      valueBoundedBy(el, min, max)) &&
    (forall i :: 0 <= i < |s| ==>
      valueBoundedBy(s[i], min, max))
  }
  predicate orderedAsc(s : seq<int>) {
    forall x, y :: 0 <= x < y < |s| ==>
      s[x] < s[y]
  }
}
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
             formula.trueLiteralsCount, formula.falseLiteralsCount;
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
             formula.trueLiteralsCount, formula.falseLiteralsCount;
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
    ensures size == 0;
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
