package ompd.analysis;

import cetus.analysis.CFGraph;
import cetus.analysis.DFANode;
import cetus.analysis.LoopTools;
import cetus.hir.*;
import ompd.hir.OMPDTools;

import java.util.HashSet;
import java.util.Set;

public class PrevDefsFinder
{
    private Procedure main;
    private CFGraph cfg;
    Set<Symbol> symbols;

    public PrevDefsFinder(Procedure mainProc, PCFGraph graph)
    {
        if (mainProc == null)
        {
            throw new IllegalArgumentException("main procedure must not be null!");
        }
        main = mainProc;

        //        if (symbolSet == null || symbolSet.isEmpty()) {
        //            throw new IllegalArgumentException("found illegal set of symbols");
        //        }

        if (graph == null)
        {
            cfg = new PCFGraph(main);
        }
        else
        {
            cfg = graph;
        }

        run();
    }

    private void run()
    {
        /* attach DEF symbols to the CFG */
        int i;

        for (i = 0; i < cfg.size(); i++)
        {
            DFANode node = cfg.getNode(i);
            Traversable t = node.getData("ir");
            if (t != null)
            {
                Set<Symbol> defSymbols = OMPDTools.getDefSymbol(t);
                node.putData("defSymbols", defSymbols);
            }
        }
    }

    public Set<Statement> getInsertionPointAfterPrevDefs(Statement start, Set<Symbol> symbols)
    {
        Set<Statement> positions = new HashSet<Statement>();

        if (symbols.isEmpty())
        {
            positions.add(OMPDTools.getZerothStatement(main.getBody()));
            return positions;
        }

        Set<Statement> prevDefStatements = getPrevDefStatements(start, symbols);

        if (prevDefStatements.isEmpty())
        {
            prevDefStatements.add(OMPDTools.getZerothStatement(main.getBody()));
        }

        /* Treat some special cases:

          1. The def statement is the initial statement of a for loop.
             In this case, the insertion position should be the first statement of the body of the for loop.

          2. The def statement is a normal statement.
             In this case, it would be better to return its outermost loop if any exists.
             However, he loop should not contain any use of the symbol.
        */

        for (Statement prevDefStatement : prevDefStatements)
        {
            if (isLoopInitialStatement(prevDefStatement))
            {
                ForLoop forLoop = (ForLoop) prevDefStatement.getParent();
                positions.add(OMPDTools.getZerothStatement((CompoundStatement) forLoop.getBody()));
            }
            else
            {
                /* get the outermost loop that does not include an use of the symbol */
                ForLoop forLoop = OMPDTools.getOuterLoopWithoutUsingSymbols(prevDefStatement, symbols);
                if (forLoop != null)
                    positions.add(forLoop);
                else
                    positions.add(prevDefStatement);
            }
        }

        return positions;
    }

    private boolean isLoopInitialStatement(Statement statement)
    {
        Traversable parent = statement.getParent();

        if (!(parent instanceof ForLoop))
            return false;

        ForLoop forLoop = (ForLoop) parent;

        if (forLoop.getInitialStatement() == statement)
            return true;
        else
            return false;
    }

    public Set<Statement> getPrevDefStatements(Statement start, Set<Symbol> symbols)
    {
        Set<DFANode> nodes = getPrevDefNodes(start, symbols);
        return getOuterStatements(nodes, start);
    }

    private Set<DFANode> getPrevDefNodes(Statement start, Set<Symbol> symbols)
    {
        Set<DFANode> nodes = new HashSet<DFANode>();
        Set<DFANode> visited = new HashSet<DFANode>();

        DFANode startNode = cfg.getNodeWith("stmt", start);
        if (startNode == null)
        {
            throw new IllegalArgumentException("start statement is unknown!\n" + start);
        }

        visited.add(startNode);

        for (DFANode pred : startNode.getPreds())
        {
            collectDefStatementsRecursively(pred, nodes, symbols, visited);
        }

        return nodes;
    }

    private Set<Statement> getOuterStatements(Set<DFANode> nodes, Statement start)
    {
        Set<Statement> statements = new HashSet<Statement>();

        for (DFANode node : nodes)
        {
            Statement statement = getOuterStatement(node, start);
            statements.add(statement);
        }

        return statements;
    }

    private Statement getOuterStatement(DFANode node, Statement start)
    {
        Statement statement;

        /* Because we attached defSymbols to IRs, we are sure that node must have "ir" key. */
        Traversable t = node.getData("ir");
        if (t instanceof Statement)
        {
            statement = (Statement) t;
        }
        else
        {
            statement = IRTools.getAncestorOfType(t, Statement.class);
        }

        //        if (statement.getParent() instanceof ForLoop) {
        //            /* It is an initialization statement of a for loop.
        //               Let's return the parent for loop instead. */
        //            statement = (Statement) statement.getParent();
        //            return statement;
        //        }
        //
        //        /* If the start statement is not in a forLoop, then
        //         * let's make the forLoop the previous DEF statement */
        //        ForLoop forLoop;
        //
        //        for (forLoop = IRTools.getAncestorOfType(statement, ForLoop.class);
        //             forLoop != null;
        //             forLoop = IRTools.getAncestorOfType(statement, ForLoop.class)) {
        //            if (!IRTools.isAncestorOf(forLoop, start)) {
        //                statement = forLoop;
        //            } else {
        //                break;
        //            }
        //        }

        return statement;
    }

    private void collectDefStatementsRecursively(DFANode current, Set<DFANode> nodes, Set<Symbol> symbols, Set<DFANode> visited)
    {
        assert nodes != null;

        if (visited.contains(current))
        {
            return;
        }
        else
        {
            visited.add(current);
        }

        Set<Symbol> defSymbols = current.getData("defSymbols");
        if (defSymbols != null)
        {
            for (Symbol symbol : symbols)
            {
                if (defSymbols.contains(symbol))
                {
                    nodes.add(current);
                    // we don't need to look up further.
                    return;
                }
            }
        }

        // not found, continue searching upwardly
        for (DFANode pred : current.getPreds())
        {
            collectDefStatementsRecursively(pred, nodes, symbols, visited);
        }
    }
}
