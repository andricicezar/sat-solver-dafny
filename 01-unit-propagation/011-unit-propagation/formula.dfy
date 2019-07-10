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
    ensures fresh(stack);
    ensures fresh(stack.stack);
    ensures fresh(truthAssignment);
    ensures fresh(trueLiteralsCount);
    ensures fresh(falseLiteralsCount);
    ensures fresh(literalsCount);
    ensures fresh(satisfiedClauses);
    ensures fresh(positiveLiteralsToClauses);
    ensures fresh(negativeLiteralsToClauses);
    ensures stack.size == 0;
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
    assert forall x :: 0 <= x < truthAssignment.Length ==> truthAssignment[x] == -1;
    assert forall x :: 0 <= x < stack.stack.Length ==> |stack.stack[x]| == 0;
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
    requires validReferences();
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();

    requires literalsCount.Length == |clauses|;
    requires trueLiteralsCount.Length == |clauses|;
    requires falseLiteralsCount.Length == |clauses|;

    requires forall value :: 0 <= value < truthAssignment.Length ==>
                truthAssignment[value] == -1;

    modifies trueLiteralsCount, falseLiteralsCount, literalsCount;

    ensures validLiteralsCount();
    ensures validTrueLiteralsCount(truthAssignment[..]);
    ensures validFalseLiteralsCount(truthAssignment[..]);
  {
    var i : int := 0;

    while (i < |clauses|)
      invariant 0 <= i <= |clauses|;
      invariant forall j :: 0 <= j < i ==> literalsCount[j] == |clauses[j]|;
      invariant forall j :: 0 <= j < i ==> trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j]);
      invariant forall j :: 0 <= j < i ==> falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j]);

      decreases |clauses| - i;
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
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount,
          falseLiteralsCount;
    
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();
    requires validLiteralsCount();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);

    requires 0 <= index < |clauses|;
  {
    trueLiteralsCount[index] == 0 &&
    literalsCount[index] - falseLiteralsCount[index] == 1
  }

  function method isEmptyClause(index : int) : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, literalsCount,
          falseLiteralsCount;
    
    requires validVariablesCount();
    requires validStack();
    requires validTruthAssignment();
    requires validClauses();
    requires validLiteralsCount();
    requires validTrueLiteralsCount(truthAssignment[..]);
    requires validFalseLiteralsCount(truthAssignment[..]);

    requires 0 <= index < |clauses|;
  {
    literalsCount[index] == falseLiteralsCount[index]
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

  method createSatisfiedClausesArray()
    requires validReferences();
    requires validVariablesCount();
    requires validClauses();
    requires validStack();
    requires validTruthAssignment();
    requires satisfiedClauses.Length == |clauses|;
    requires forall value :: 0 <= value < truthAssignment.Length ==>
                truthAssignment[value] == -1;

    modifies satisfiedClauses;

    ensures validSatisfiedClauses(truthAssignment[..]);
  {
    var i := 0;

    while (i < |clauses|)
      invariant 0 <= i <= |clauses|;
      invariant forall j :: 0 <= j < i ==> 
        satisfiedClauses[j] == isClauseSatisfied(truthAssignment[..], j);
      decreases |clauses| - i;
    {
      assert validClause(clauses[i]);
      assert forall value :: 0 <= value < truthAssignment.Length ==>
                truthAssignment[value] == -1;
      assert forall literal :: literal in clauses[i] ==>
              getLiteralValue(truthAssignment[..], literal) == -1;
      assert isClauseSatisfied(truthAssignment[..], i) == false;
      satisfiedClauses[i] := false;
      i := i + 1;
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
             falseLiteralsCount, satisfiedClauses;

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
               falseLiteralsCount, satisfiedClauses;

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

      invariant forall cI :: 0 <= cI < |clauses| ==>
        satisfiedClauses[cI] == isClauseSatisfied(truthAssignment[..], cI);

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
        modifies trueLiteralsCount, satisfiedClauses;

        invariant 0 <= i <= |positivelyImpactedClauses|;
        /* invariant trueLiteralsCount.Length == |clauses|;*/

        invariant forall i' :: 0 <= i' < |clauses| && i' !in positivelyImpactedClauses ==>
          trueLiteralsCount[i']
            == countTrueLiterals(newTau, clauses[i']);

        invariant forall i' :: 0 <= i' < i ==>
          trueLiteralsCount[positivelyImpactedClauses[i']]
            == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']]);

        invariant forall i' :: i <= i' < |positivelyImpactedClauses| ==>
          trueLiteralsCount[positivelyImpactedClauses[i']]
            == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']]);

        invariant forall i' :: 0 <= i' < |clauses| && i' !in positivelyImpactedClauses ==>
          satisfiedClauses[i']
            == isClauseSatisfied(newTau, i');

        invariant forall i' :: 0 <= i' < i ==>
          satisfiedClauses[positivelyImpactedClauses[i']]
            == isClauseSatisfied(newTau, positivelyImpactedClauses[i']);

        invariant forall i' :: i <= i' < |positivelyImpactedClauses| ==>
          satisfiedClauses[positivelyImpactedClauses[i']]
            == isClauseSatisfied(previousTau, positivelyImpactedClauses[i']);
      {
        var clauseIndex := positivelyImpactedClauses[i];
        var clause := clauses[clauseIndex];
        assert validClause(clause);

        unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
        trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;

        if (trueLiteralsCount[clauseIndex] == 0) {
          countTrueLiterals0_noLiteralsTrue(newTau, clause);
          satisfiedClauses[clauseIndex] := false;
        } else {
          countTrueLiteralsX_existsTrueLiteral(newTau, clause);
        }

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
             satisfiedClauses, falseLiteralsCount;

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
      modifies trueLiteralsCount, satisfiedClauses;

      invariant 0 <= i <= |impactedClauses|;

      invariant forall j :: 0 <= j < |clauses| && j !in impactedClauses
        ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j]);

      invariant forall cI :: 0 <= cI < |clauses| && cI !in impactedClauses ==>
        satisfiedClauses[cI] == isClauseSatisfied(newTau, cI) == old(satisfiedClauses[cI]);

      invariant forall j :: 0 <= j < i ==>
        trueLiteralsCount[impactedClauses[j]] 
          == countTrueLiterals(newTau, clauses[impactedClauses[j]]);

      invariant forall j :: i <= j < |impactedClauses| ==>
        trueLiteralsCount[impactedClauses[j]]
          == countTrueLiterals(oldTau, clauses[impactedClauses[j]]);

      invariant forall j :: 0 <= j < i ==>
        satisfiedClauses[impactedClauses[j]] 
          == isClauseSatisfied(newTau, impactedClauses[j]);

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
      satisfiedClauses[clauseIndex] := true;

      assert trueLiteral in clauses[clauseIndex]
        && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);

      i := i + 1;
    }

    assert validTrueLiteralsCount(newTau);
    assert validSatisfiedClauses(newTau);

    /* toate clauzele care au negatia variabilei*/
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
    assert validSatisfiedClauses(truthAssignment[..]);
    assert validTrueLiteralsCount(truthAssignment[..]);
    assert validFalseLiteralsCount(truthAssignment[..]);
    assert validLiteralsCount();
    assert validPositiveLiteralsToClauses();
    assert validNegativeLiteralsToClauses();
  }

  function method hasEmptyClause() : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, literalsCount, satisfiedClauses, 
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    ensures hasEmptyClause() == true ==> 
      exists i :: 0 <= i < |clauses| 
               && falseLiteralsCount[i] == literalsCount[i];
    ensures hasEmptyClause() == false ==>
      forall i :: 0 <= i < |clauses| ==>
        falseLiteralsCount[i] < literalsCount[i];
  {
    if i : int :| 0 <= i < |clauses| && falseLiteralsCount[i] == literalsCount[i] 
      then true
      else false
  }

  function method isEmpty() : bool
    reads this, stack, stack.stack, truthAssignment, trueLiteralsCount, 
          falseLiteralsCount, literalsCount, satisfiedClauses, 
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
          falseLiteralsCount[k] < literalsCount[k];

        while (k < |clauses|)
          invariant 0 <= k <= |clauses|;
          invariant forall k' :: 0 <= k' < k ==>
                      trueLiteralsCount[k'] > 0;

          decreases |clauses| - k;
        {
          assert validClause(clauses[k]);
          assert falseLiteralsCount[k] < literalsCount[k];

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
    requires falseLiteralsCount[cI] < literalsCount[cI];

    ensures trueLiteralsCount[cI] > 0;
  {
    var tau := truthAssignment[..];
    var clause := clauses[cI];

    assert forall x :: x in clause ==>
      getLiteralValue(tau, x) in [0, 1];

    if forall x :: x in clause ==> getLiteralValue(tau, x) == 0 {
      /* assert falseLiteralsCount[cI] == literalsCount[cI];*/

      var k := |clause| - 1;

      while (k > 0)
        invariant 0 <= k <= |clause|;

        invariant countFalseLiterals(tau, clause[k..]) == |clause| - k;

        decreases k;
      {
        k := k - 1;
      }

      assert countFalseLiterals(tau, clause) == |clause| == literalsCount[cI];
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
    // TODO: take care not to repeat the selection...
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
             falseLiteralsCount, satisfiedClauses;

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
    /* print literal, " ", value, ", ";*/
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
        falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex]) {

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
    requires falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex];

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
               && falseLiteralsCount[clauseIndex] == literalsCount[clauseIndex];
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
    requires falseLiteralsCount[clauseIndex] == literalsCount[clauseIndex];
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

    // is unit
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
    requires validLiteralsCount();
    requires 0 <= clauseIndex < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires validLiteral(literal);
    requires trueLiteralsCount[clauseIndex] == 0;
    requires falseLiteralsCount[clauseIndex] + 1 == literalsCount[clauseIndex];
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
