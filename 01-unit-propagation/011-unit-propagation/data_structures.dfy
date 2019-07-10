include "concerns/seq-predicates.dfy"
include "utils.dfy"
include "stack.dfy"

trait DataStructures { 
  var variablesCount : int;
  var clauses : seq<seq<int>>;

  var stack : Stack;
  var truthAssignment : array<int>; // from 0 to variablesCount - 1, values: -1, 0, 1

  var satisfiedClauses: array<bool>; // from 0 to |clauses| - 1

  var trueLiteralsCount : array<int>; // from 0 to |clauses| - 1
  var falseLiteralsCount : array<int>; // from 0 to |clauses| - 1
  var literalsCount : array<int>; // from 0 to |clauses| - 1

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

  predicate validSatisfiedClauses(truthAssignment : seq<int>)
    reads this, stack, stack.stack, satisfiedClauses;
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
  {
    satisfiedClauses.Length == |clauses| &&
    forall i :: 0 <= i < satisfiedClauses.Length ==>
      satisfiedClauses[i] == isClauseSatisfied(truthAssignment, i)  
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

  predicate validLiteralsCount()
    reads this, literalsCount;
    requires validVariablesCount();
    requires validClauses();
  {
    literalsCount.Length == |clauses| &&
    forall i :: 0 <= i < |clauses| ==>
      literalsCount[i] == |clauses[i]|
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

    // toate clausele care apar in array contin variabila
    (forall clauseIndex :: clauseIndex in s ==>
      variable+1 in clauses[clauseIndex]) &&

    // clauzele care nu apar in array, nu contin variabila
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

    // toate clausele care apar in array contin variabila
    (forall clauseIndex :: clauseIndex in s ==>
      -variable-1 in clauses[clauseIndex]) &&

    // clauzele care nu apar in array, nu contin variabila
    (forall clauseIndex :: 0 <= clauseIndex < |clauses| && clauseIndex !in s ==>
      -variable-1 !in clauses[clauseIndex])
  }

  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount,
          literalsCount, positiveLiteralsToClauses, negativeLiteralsToClauses;
  {
    (truthAssignment != trueLiteralsCount) &&
    (truthAssignment != falseLiteralsCount) &&
    (truthAssignment != literalsCount) &&
    (trueLiteralsCount != falseLiteralsCount) &&
    (trueLiteralsCount != literalsCount) &&
    (falseLiteralsCount != literalsCount) &&
    (positiveLiteralsToClauses != negativeLiteralsToClauses)
  }

  predicate valid() 
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, literalsCount, satisfiedClauses, 
          positiveLiteralsToClauses, negativeLiteralsToClauses;
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
    requires falseLiteralsCount[i] < literalsCount[i];
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
        invariant 0 <= k < |clause| == literalsCount[i];
        invariant countFalseLiterals(truthAssignment[..], clause[k..]) == |clause| - k;
        decreases k;
      {
        assert getLiteralValue(truthAssignment[..], clause[k]) == 0;
        k := k - 1;
      }

      assert countFalseLiterals(truthAssignment[..], clause) == literalsCount[i];
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
