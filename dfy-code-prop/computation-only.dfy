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
function method convertLVtoVI(literal : int, value : bool) : (int, int) reads this; requires validVariablesCount();requires validLiteral(literal);ensures validVariable(convertLVtoVI(literal, value).0);ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal);ensures convertLVtoVI(literal, value).1 in [0,1];{var variable := getVariableFromLiteral(literal);var v := if value then 1 else 0;var val := if literal < 0 then 1-v else v;(variable, val)}
function method getVariableFromLiteral(literal : int) : int reads this;requires validVariablesCount();requires validLiteral(literal);ensures validVariable(getVariableFromLiteral(literal));{Utils.abs(literal)-1}
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
{
this.variablesCount := variablesCount;
this.clauses := clauses;
this.stack := new Stack(variablesCount);
new;
this.truthAssignment :=
Utils.newInitializedSeq(variablesCount, -1);
this.trueLiteralsCount := new int[|this.clauses|];
this.falseLiteralsCount := new int[|this.clauses|];
positiveLiteralsToClauses := new seq<int>[variablesCount];
negativeLiteralsToClauses := new seq<int>[variablesCount];
this.createTFLArrays();
this.createPositiveLiteralsToClauses();
this.createNegativeLiteralsToClauses();
}
method createTFLArrays()
{
var i : int := 0;
while (i < |clauses|)
{
trueLiteralsCount[i] := 0;
falseLiteralsCount[i] := 0;
i := i + 1;
}
}
function method isUnitClause(index : int) : bool
falseLiteralsCount;
{
trueLiteralsCount[index] == 0 &&
|clauses[index]| - falseLiteralsCount[index] == 1
}
function method isEmptyClause(index : int) : bool
{
|clauses[index]| == falseLiteralsCount[index]
}
method createPositiveLiteralsToClauses()
{
var variable := 0;
while (variable < variablesCount)
{
positiveLiteralsToClauses[variable] := [];
var clauseIndex := 0;
while (clauseIndex < |clauses|)
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
{
var variable := 0;
while (variable < variablesCount)
{
negativeLiteralsToClauses[variable] := [];
var clauseIndex := 0;
while (clauseIndex < |clauses|)
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
stack.stack[i] == old(stack.stack[i]);
{
stack.createNewLayer();
}
method undoLayerOnStack() 
{
var k := 0;
var layer := stack.stack[stack.size-1];
stack.stack[stack.size-1] := [];
stack.size := stack.size - 1;
while (k < |layer|) 
{
var x := layer[k];
k := k + 1;
var (variable, value) := x;
truthAssignment[variable] := -1;
stack.contents := stack.contents - {x};
var positivelyImpactedClauses := positiveLiteralsToClauses[variable]; // decrease true counter
var negativelyImpactedClauses := negativeLiteralsToClauses[variable];// decrease false counters
if (!value) {
negativelyImpactedClauses := positiveLiteralsToClauses[variable]; // decrease true counter
positivelyImpactedClauses := negativeLiteralsToClauses[variable];// decrease false counters
}
var i := 0;
while (i < |positivelyImpactedClauses|)
{
var clauseIndex := positivelyImpactedClauses[i];
var clause := clauses[clauseIndex];
trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;
i := i + 1;
}
i := 0;
while (i < |negativelyImpactedClauses|)
{
var clauseIndex := negativelyImpactedClauses[i];
falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
i := i + 1;
}
}
}
method setVariable(variable : int, value : bool) 
{
var el := (variable, value);
var iL := stack.size - 1; // index layer
stack.stack[iL] := stack.stack[iL] + [el];
stack.contents := stack.contents + {el};
if (value) {
truthAssignment[variable] := 1;
} else {
truthAssignment[variable] := 0;
}
var trueLiteral := variable+1;
var falseLiteral := -variable-1;
if (!value) {
trueLiteral := -variable-1;
falseLiteral := variable+1;
}
var i := 0;
var impactedClauses := positiveLiteralsToClauses[variable];
var impactedClauses' := negativeLiteralsToClauses[variable];
if (!value) {
impactedClauses := negativeLiteralsToClauses[variable];
impactedClauses' := positiveLiteralsToClauses[variable];
}
while (i < |impactedClauses|)
{
var clauseIndex := impactedClauses[i];
trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;
i := i + 1;
}
var i' := 0;
while (i' < |impactedClauses'|)
{
var clauseIndex := impactedClauses'[i'];
falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;
i' := i' + 1;
}
}
function method hasEmptyClause() : bool
{
if i : int :| 0 <= i < |clauses| && falseLiteralsCount[i] == |clauses[i]|
then true
else false
}
function method isEmpty() : bool
{
if i : int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0 
then false
else true
}
method chooseLiteral() returns (x : int)
{
var i : int :| 0 <= i < |clauses| && trueLiteralsCount[i] == 0; 
notDone_literalsToSet(i);
var literal :| literal in clauses[i] 
&& truthAssignment[getVariableFromLiteral(literal)] == -1;
return literal;
}
method setLiteral(literal : int, value : bool)
{
var variable := getVariableFromLiteral(literal);
var value' := if literal > 0 then value else !value;
setVariable(variable, value');
var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
var k := 0;
while (k < |negativelyImpactedClauses|) 
{
var clauseIndex := negativelyImpactedClauses[k];
var clause := clauses[clauseIndex];
if (trueLiteralsCount[clauseIndex] == 0 &&
falseLiteralsCount[clauseIndex] + 1 == |clauses[clauseIndex]|) {
var literal :| literal in clause 
&& truthAssignment[getVariableFromLiteral(literal)] == -1;
setLiteral(literal, true);
unsetVariablesCount := countUnsetVariables(truthAssignment[..]);
}
k := k + 1;
}
}
method render(truthAssignment : seq<int>) 
{
var clauseIndex := 0;
print "Solution:\n", truthAssignment, "\n\nClauses:\n";
while (clauseIndex < |clauses|) 
{
var clause := clauses[clauseIndex];
var literalIndex := 0;
while (literalIndex < |clause|) 
{
var literal := clause[literalIndex];
print literal;
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
include "parser.dfy"
include "file_input.dfy"
include "my_datatypes.dfy"
module Input {
import Parser
import FileInput
import opened MyDatatypes
function method getInput() : Maybe<(int, seq<seq<int>>)> 
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
{
var j := 0;
var min := variablesCount+1;
while (j < |clause|)
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
{
var newClause := sort(variablesCount, clauses[k]);
newClauses := newClauses + [newClause];
k := k + 1;
}
}
method Main() 
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
{
if |content| == 0 then content
else
if content[0] == '\n' then content[1..] 
else skipLine(content[1..])
}
function method skipWhiteSpaces(content : string) : string 
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
{
(chr as int) - ('0' as int)
}
function method extractDigits(content : string) : (seq<int>, string)
{
if (|content| == 0) then ([], content)
else if (isDigit(content[0])) then
var (h, tail) := extractDigits(content[1..]);
([toInt(content[0])] + h, tail)
else ([], content)
}
function method joinInts(number : int, ints : seq<int>) : int 
{
if |ints| == 0 then number
else joinInts(number * 10 + ints[0], ints[1..])
}
function method getNextNumber(content : string) : Maybe<(int, string)>
{
if (|content| == 0) then Error("content finished unexpectatly")
else if (content[0] == '-') then
var (digits, newContent) := extractDigits(content[1..]);
if |digits| == 0 then Error("only alpha characters ahead, no numbers after -")
else
var number := joinInts(0, digits);
Just((-number, newContent))
else
var (digits, newContent) := extractDigits(content);
if |digits| == 0 then Error("only alpha characters ahead, no numbers")
else 
var number := joinInts(0, digits);
Just((number, newContent))
}
function method extractNumbers(content : string) : (seq<int>, string)
{
var content' := skipWhiteSpaces(content);
match getNextNumber(content')
case Error(_) => ([], content')
case Just((number, content'')) =>
var content''' := skipWhiteSpaces(content'');
var (fst, snd) := extractNumbers(content''');
([number] + fst, snd)
}
function method getNextClause(numbers : seq<int>) : Maybe<(seq<int>, seq<int>)>
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
}
include "formula.dfy"
datatype SAT_UNSAT = SAT(tau:seq<int>) | UNSAT
class SATSolver {
var formula : Formula;
constructor(f' : Formula)
{
formula := f';
}
method step(literal : int, value : bool) returns (result : SAT_UNSAT)
{
formula.newLayerOnStack();
formula.setLiteral(literal, value);
result := solve();
formula.undoLayerOnStack();
if (formula.truthAssignment[..] != old(formula.truthAssignment[..])) {
var i :| 0 <= i < formula.truthAssignment.Length && 
formula.truthAssignment[i] != old(formula.truthAssignment[i]);
var y := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
}
return result;
}
method solve() returns (result : SAT_UNSAT) 
{
if (formula.hasEmptyClause()) {
return UNSAT;
}
if (formula.isEmpty()) {
result := SAT(formula.truthAssignment[..]);
return result;
}
var literal := formula.chooseLiteral();
result := step(literal, true);
if (result.SAT?) { 
return result;
}
result := step(literal, false);
return result;
}
}
class Stack {
var size : int;
var stack : array<seq<(int, bool)>>;
var variablesCount : int;
constructor(varCount : int) 
{
this.size := 0;
this.variablesCount := varCount;
this.stack := new seq<(int, bool)>[varCount];
this.contents := {};
new;
var i := 0;
while (i < stack.Length) 
{
stack[i] := [];
i := i + 1;
}
}
}
module Utils {
method newInitializedSeq(n: int, d: int) returns (r : array<int>)
{
r := new int[n];
var index : int := 0;
while (index < n)
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
}
