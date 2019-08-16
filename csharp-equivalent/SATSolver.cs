using System;
using System.IO;
using System.Collections.Generic;

namespace satsolver 
{
    class Formula
    {
        private int variablesCount;
        private int clausesCount;

        private int[][] clauses;

        private Stack< Stack<(int, bool)> > stack = new Stack< Stack<(int, bool)> >();
        private int[] truthAssignment;
        private int[] trueLiteralsCount;
        private int[] falseLiteralsCount;

        private int[][] positiveLiteralsToClauses;
        private int[][] negativeLiteralsToClauses;

        public Formula(int varC, int clsC, int[][] cls) {
            variablesCount = varC;
            clausesCount = clsC;
            clauses = cls;

            truthAssignment = new int[variablesCount];
            Array.Fill(truthAssignment, -1);

            trueLiteralsCount = new int[clausesCount];
            Array.Fill(trueLiteralsCount, 0);
            falseLiteralsCount = new int[clausesCount];
            Array.Fill(falseLiteralsCount, 0);

            positiveLiteralsToClauses = new int[variablesCount][];
            for (int i = 0; i < variablesCount; ++i) {
                positiveLiteralsToClauses[i] = new int[clausesCount+1];
                Array.Fill(positiveLiteralsToClauses[i], 0);
            }
            negativeLiteralsToClauses = new int[variablesCount][];
            for (int i = 0; i < variablesCount; ++i) {
                negativeLiteralsToClauses[i] = new int[clausesCount+1];
                Array.Fill(negativeLiteralsToClauses[i], 0);
            }

            createPositiveNegativeLiteralsToClauses();
        }

        void createPositiveNegativeLiteralsToClauses() {
            for (int i = 0; i < clausesCount; ++i) {
                for (int j = 1; j <= clauses[i][0]; ++j) {
                    if (clauses[i][j] > 0) {
                        positiveLiteralsToClauses
                            [clauses[i][j]-1]
                            [++positiveLiteralsToClauses[clauses[i][j]-1][0]] = i;
                    } else if (clauses[i][j] < 0) {
                        negativeLiteralsToClauses
                            [-clauses[i][j]-1]
                            [++negativeLiteralsToClauses[-clauses[i][j]-1][0]] = i;
                    }
                }
            }
        }

        void undoLayerOnStack() {
            Stack<(int, bool)> layer = stack.Pop();

            while (layer.Count > 0) {
                (int variable, bool value) = layer.Pop();
                truthAssignment[variable] = -1;

                int[] positivelyImpacted = positiveLiteralsToClauses[variable];
                int[] negativelyImpacted = negativeLiteralsToClauses[variable];

                if (!value) {
                    negativelyImpacted = positiveLiteralsToClauses[variable];
                    positivelyImpacted = negativeLiteralsToClauses[variable];
                }

                for (int i = 1; i <= positivelyImpacted[0]; ++i)
                    trueLiteralsCount[positivelyImpacted[i]] -= 1;
                for (int i = 1; i <= negativelyImpacted[0]; ++i)
                    falseLiteralsCount[negativelyImpacted[i]] -= 1;
            }
        }

        void setVariable(int variable, bool value) {
            truthAssignment[variable] = value ? 1 : 0;
            stack.Peek().Push((variable, value));

            int[] positivelyImpacted = positiveLiteralsToClauses[variable];
            int[] negativelyImpacted = negativeLiteralsToClauses[variable];

            if (!value) {
                negativelyImpacted = positiveLiteralsToClauses[variable];
                positivelyImpacted = negativeLiteralsToClauses[variable];
            }

            for (int i = 1; i <= positivelyImpacted[0]; ++i)
                trueLiteralsCount[positivelyImpacted[i]] += 1;
            for (int i = 1; i <= negativelyImpacted[0]; ++i)
                falseLiteralsCount[negativelyImpacted[i]] += 1;
        }

        void setLiteral(int literal, bool value) {
            int variable = (literal < 0) ? -literal-1 : literal-1;
            value = (literal < 0) ? !value : value;
            setVariable(variable, value);

            int[] negativelyImpacted = negativeLiteralsToClauses[variable];
            for (int i = 1; i <= negativelyImpacted[0]; ++i) {
                if (clauses[negativelyImpacted[i]][0] - 1 == falseLiteralsCount[negativelyImpacted[i]]
                    && trueLiteralsCount[negativelyImpacted[i]] == 0) {
                    for (int j = 1; j <= clauses[negativelyImpacted[i]][0]; ++j) {
                        int literal_l = clauses[negativelyImpacted[i]][j];
                        int variable_l = (literal_l < 0) ? -literal_l-1 : literal_l-1;
                        if (truthAssignment[variable_l] == -1) {
                            setLiteral(literal_l, true);
                        }
                    }
                }
            }
        }

        void newLayerOnStack() {
            stack.Push(new Stack<(int, bool)>());
        }

        bool step(int literal, bool value) {
            newLayerOnStack();
            setLiteral(literal, value);
            bool result = solve();
            undoLayerOnStack();
            return result;
        }

        bool hasEmptyClauses() {
            for (int i = 0; i < clausesCount; ++i)
                if (clauses[i][0] == falseLiteralsCount[i])
                    return true;

            return false;
        }
        
        bool isEmpty() {
            for (int i = 0; i < clausesCount; ++i)
                if (trueLiteralsCount[i] == 0)
                    return false;

            return true;
        }
        int chooseLiteral() {
            for (int i = 0; i < clausesCount; ++i)
                if (trueLiteralsCount[i] == 0) {
                    for (int j = 1; j <= clauses[i][0]; ++j) {
                        int literal_l = clauses[i][j];
                        int variable_l = (literal_l < 0) ? -literal_l-1 : literal_l-1;
                        if (truthAssignment[variable_l] == -1) {
                            return literal_l;
                        }
                    }
                }

            return 2; // never
        }
        public bool solve() {
            if (hasEmptyClauses()) return false;
            if (isEmpty()) return true;

            int literal = chooseLiteral();
            if (step(literal, true)) {
                return true;
            }
            return step(literal, false);
        }
    }

    class SATSolver 
    {
        static int Main(string[] args) 
        {
            Console.WriteLine("Starting...");

            if (args.Length == 0) {
                System.Console.WriteLine("Please enter a path.");
                return 1;
            }

            Console.WriteLine(args[0]);
            
            int variablesCount = 0;
            int clausesCount = 0;
            int[][] clauses = new int[7000][];
            int currentClause = 0;

            // inspired from https://github.com/helium729/heliSAT-legacy
            StreamReader reader = new StreamReader(args[0]);
            while (!reader.EndOfStream) {
              var line = reader.ReadLine();
              if (line == "")
                continue;
              var splited = line.Split(" ", StringSplitOptions.RemoveEmptyEntries);
              if (splited[0] == "c")
                continue;
              else if (splited[0] == "p") {
                variablesCount = Convert.ToInt32(splited[2]);
                clauses[0] = new int[variablesCount*2+1];
                Array.Fill(clauses[0], 0);
                clausesCount = Convert.ToInt32(splited[3]);
                continue;
              } else {
                foreach (var a in splited) {
                  if (a == "0") {     
                    ++currentClause;
                    clauses[currentClause] = new int[variablesCount*2+1];
                    Array.Fill(clauses[currentClause], 0);
                    // Console.WriteLine("Clause: [{0}]", string.Join(", ", clauses[currentClause]));
                    break;
                  }
                  int temp = Convert.ToInt32(a);
                  clauses[currentClause][++clauses[currentClause][0]] = temp;
                }
              }
            }

            long tl = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            Formula formula = new Formula(variablesCount, clausesCount, clauses);
            long tlf = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();

            if (formula.solve()) {
                Console.WriteLine("SAT");
            } else {
                Console.WriteLine("UNSAT");
            }

            Console.WriteLine("Time to solve {0}s", ((double)tlf-tl)/1000.0);

            return 0;
        }
    }
}
