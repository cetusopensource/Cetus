package ompd.transforms;

import cetus.analysis.CFGraph;
import cetus.analysis.DFANode;
import cetus.analysis.Section;
import cetus.hir.*;
import ompd.analysis.PrevDefsFinder;
import ompd.hir.OMPDTools;
import ompd.hir.OmpdAnnotation;

import java.lang.reflect.Array;
import java.util.*;

public class InfUseHandler
{
    private int debug_tab = 0;
    private int debug_level;

    private Procedure mainProc;
    private Map range_map;
    private CFGraph cfg;
    private Set<Symbol> shared_vars;

    private Symbol pidSymbol;
    private Symbol iSymbol;
    private Symbol nprocSymbol;

    private TranslationUnit tu; // from mainProc

    /**
     * @param main          IR tree entry for the main procedure
     * @param i_cfg         CFG for data flow analysis already obtained
     * @param i_range_map   range map already obtained
     * @param ishvars       shared array symbol information already obtained
     * @param pid_symbol
     * @param i_symbol
     * @param nprocs_symbol
     */
    public InfUseHandler(Procedure main, CFGraph i_cfg, Map i_range_map, Set<Symbol> ishvars, Symbol pid_symbol, Symbol i_symbol, Symbol nprocs_symbol)
    {
        mainProc = main;
        cfg = i_cfg;
        range_map = i_range_map;
        shared_vars = ishvars;

        this.pidSymbol = pid_symbol;
        this.iSymbol = i_symbol;
        this.nprocSymbol = nprocs_symbol;

        tu = IRTools.getAncestorOfType(mainProc, TranslationUnit.class);
    }

    public String getPassName()
    {
        return "[InfUseHandler]";
    }

    /**
     * The main driver method to call the INF USE handler.
     */
    public void run()
    {
        Set<DFANode> barriers = OMPDTools.collectBarrierNodes(cfg);
        for (DFANode barrier : barriers)
        {
            Set<Symbol> symbols = getInterestingUseSymbols(barrier);

            if (!isValidTransformation(barrier, symbols))
            {
                continue;
            }

            Section.MAP intra_liveout = barrier.getData("intra_liveout");

            for (Symbol symbol : symbols)
            {
                Section useSection = intra_liveout.get(symbol);

                /* we are sure that the useSection is a single INF section.
                 * because it was checked in isValidTransform(). */
                handleInfUse(barrier, symbol, useSection);
            }

            restoreOriginalLoop(barrier, symbols);
            serializeForLoop(barrier, symbols);
        }
    }

    /**
     * This method selects interesting symbols from a set of symbols. Interesting symbols
     * are those whose section is related to the partitioned iterator. Thus, sections with
     * ompd_lb# and ompd_ub is one of the interesting sections, and [-INF:+INF] sections
     * whose access expression is related to the iterator is also interesting.
     *
     * @param barrier
     * @return
     */
    private Set<Symbol> getInterestingUseSymbols(DFANode barrier)
    {
        Set<Symbol> symbols = new HashSet<Symbol>();
        Section.MAP intra_liveout = barrier.getData("intra_liveout");

        Set<Symbol> candidates = intra_liveout.keySet();
        for (Symbol symbol : candidates)
        {
            Section section = intra_liveout.get(symbol);

            if (OMPDTools.isSingleInfSection(section))
            {
                // TODO: check the source of INF is related to the iterator.
                symbols.add(symbol);
            }

            // TODO: add checking of partitioned sections
        }

        return symbols;
    }

    private ForLoop nextForLoop(DFANode barrier, Set<Symbol> symbols)
    {
        if (symbols.isEmpty())
        {
            return null;
        }

        List<Symbol> list = new ArrayList<Symbol>(symbols);

        ForLoop forLoop1;
        forLoop1 = nextForLoop(barrier, list.get(0));
        if (forLoop1 == null)
        {
            return null;
        }

        for (int i = 1; i < list.size(); i++)
        {
            ForLoop forLoop2 = nextForLoop(barrier, list.get(i));
            if (forLoop1 != forLoop2)
            {
                return null;
            }
        }

        return forLoop1;
    }

    private void restoreOriginalLoop(DFANode barrier, Set<Symbol> symbols)
    {
        ForLoop forLoop = nextForLoop(barrier, symbols);

        if (forLoop == null)
        {
            return;
        }

        /* restore the original initialization and condition expressions. */
        OmpdAnnotation ompdAnnotation = forLoop.getAnnotation(OmpdAnnotation.class, "for");
        if (ompdAnnotation != null)
        {
            forLoop.setInitialStatement((Statement) ompdAnnotation.get("origInitStmt"));
            forLoop.setCondition((Expression) ompdAnnotation.get("origCondExpr"));
        }
    }

    private void serializeForLoop(DFANode barrier, Set<Symbol> symbols)
    {
        ForLoop forLoop = nextForLoop(barrier, symbols);

        if (forLoop == null)
        {
            return;
        }

        /* serialize the omp for: for -> for_guided */
        OmpdAnnotation ompdAnnotation = forLoop.getAnnotation(OmpdAnnotation.class, "for");
        if (ompdAnnotation != null)
        {
            ompdAnnotation.remove("for");
            ompdAnnotation.put("for_guided", true);
        }
    }

    private boolean isValidTransformation(DFANode barrier, Set<Symbol> symbols)
    {
        /* check the symbols are in a single for loop */
        ForLoop forLoop = nextForLoop(barrier, symbols);
        if (forLoop == null)
        {
            return false;
        }

        /* check USE sections of these symbols are all [-INF:+INF] */
        Section.MAP sectionMap = barrier.getData("intra_liveout");
        if (sectionMap == null || sectionMap.isEmpty())
        {
            return false;
        }

        for (Symbol symbol : symbols)
        {
            Section section = sectionMap.get(symbol);
            if (section == null || !OMPDTools.isSingleInfSection(section))
            {
                return false;
            }

            List<Section> defSections = previousDefSection(barrier, symbol);
            if (defSections == null)
                return false;

            /* TODO: support multiple previous DEF sections with one [-INF:+INF] use section */
            if (defSections.size() != 1)
                return false;

            Section defSection = defSections.get(0);

            /* To simplify the problem, the current compiler assumes a few things as follows:
             * 1. Single read access between this barrier and the next barrier.
             * 2. Read access within a parallel loop
             * 3. one to one mapping between each iteration and read access
             *    a. just a single parallel for loop (simplest case)
             */
            //        if (!checkSingleAccess(barrier, symbol))
            //            return;

            if (hasForLoop(forLoop))
                return false;

            int partitionedDim = partitionedDimension(defSection);
            if (partitionedDim == -1)
                return false;
        }

        return true;
    }

    private void handleInfUse(DFANode barrier, Symbol symbol, Section useSection)
    {
        List<Section> defSections = previousDefSection(barrier, symbol);
        if (defSections == null)
            return;

        /* TODO: support multiple previous DEF sections with one [-INF:+INF] use section */
        assert defSections.size() == 1;
        Section defSection = defSections.get(0);

        /* To simplify the problem, the current compiler assumes a few things as follows:
         * 1. Single read access between this barrier and the next barrier.
         * 2. Read access within a parallel loop
         * 3. one to one mapping between each iteration and read access
         *    a. just a single parallel for loop (simplest case)
         */
        //        if (!checkSingleAccess(barrier, symbol))
        //            return;

        ForLoop forLoop = nextForLoop(barrier, symbol);
        assert forLoop != null;
        assert !hasForLoop(forLoop);

        int partitionedDim = partitionedDimension(defSection);
        assert partitionedDim != -1;

        /* Find the single array read access in the parallel for loop.
         * The array access expression is the source of [-INF:+INF] USE. */
        ArrayAccess arrayAccess = findArrayAccess(forLoop, symbol);
        Expression accessExpression = arrayAccess.getIndex(partitionedDim);
        Statement accessStatement = IRTools.getAncestorOfType(arrayAccess, Statement.class);

        /* get the expression for the size of the partitioned dimension. */
        List<ArraySpecifier> specifiers = symbol.getArraySpecifiers();
        ArraySpecifier specifier = specifiers.get(0);
        Expression sizeExpression = specifier.getDimension(partitionedDim);

        /* set up ompd_lb#[] and ompd_ub#[] based on the size above
         * this can also be done based on the defSection, but it will be more complicated.
         * input:
         *   1) sizeExpression
         *   2) statement after which the bound loop will be inserted. */
        // TODO: FIX null! Or can we make this thing happen later by another pass?
        // TODO: because one function doing so many things is bad.
        Expression lbExpression = new IntegerLiteral(0);
        Expression ubExpression = Symbolic.subtract(sizeExpression, new IntegerLiteral(1));
        Set<Symbol> useSymbols = DataFlowTools.getUseSymbol(sizeExpression);
        PrevDefsFinder finder = new PrevDefsFinder(mainProc, null);
        Set<Statement> defStatements = finder.getInsertionPointAfterPrevDefs(forLoop, useSymbols);

        int loopId = LoopPartition.findLoopId(defStatements, lbExpression, ubExpression);

        if (loopId == -1)
        {
            /* allocate a new loop id and declare related variables */
            loopId = LoopPartition.getNewLoopId();

            LoopPartition.createBoundInitLoop(tu, loopId, defStatements, lbExpression, ubExpression);
        }

        Symbol lbSymbol, ubSymbol;
        lbSymbol = OMPDTools.getlbSymbol(tu, loopId);
        ubSymbol = OMPDTools.getubSymbol(tu, loopId);

        /* enclose the access statement by if statement with
         * these ompd_lb#[ompd_procid] and ompd_ub#[ompd_procid].
         *
         * Output:
         *   if (expr >= ompd_lb#[ompd_procid] && expr <= ompd_ub#[ompd_procid]) {
         *       original statement;
         *   }
         */
        Expression ompdLBExpression = OMPDTools.createArrayAccess(lbSymbol, pidSymbol);
        Expression ompdUBExpression = OMPDTools.createArrayAccess(ubSymbol, pidSymbol);
        BinaryExpression condition1 = new BinaryExpression(accessExpression.clone(), BinaryOperator.COMPARE_GE, ompdLBExpression);
        BinaryExpression condition2 = new BinaryExpression(accessExpression.clone(), BinaryOperator.COMPARE_LE, ompdUBExpression);
        BinaryExpression condition = new BinaryExpression(condition1, BinaryOperator.LOGICAL_AND, condition2);
        IfStatement ifStatement = new IfStatement(condition, accessStatement.clone());
        accessStatement.swapWith(ifStatement); // actually overwriting is needed, not swapping

        /* replace USE information from the guided read access */
        assert useSection.size() == 1;
        Section.ELEMENT element = useSection.get(0);
        RangeExpression rangeExpression = new RangeExpression(ompdLBExpression.clone(), ompdUBExpression.clone());
        element.remove(partitionedDim); // remove the [-INF:+INF] range expression
        element.add(partitionedDim, rangeExpression);

    }

    private ArrayAccess findArrayAccess(ForLoop forLoop, Symbol symbol)
    {
        DepthFirstIterator iterator = new DepthFirstIterator(forLoop);
        while (iterator.hasNext())
        {
            Object obj = iterator.next();
            if (obj instanceof ArrayAccess)
            {
                ArrayAccess arrayAccess = (ArrayAccess) obj;
                if (arrayAccess.getArrayName().toString().equals(symbol.getSymbolName()))
                    return arrayAccess;
            }
        }
        return null;
    }

    private boolean hasForLoop(ForLoop forLoop)
    {
        return IRTools.containsClass(forLoop.getBody(), ForLoop.class);
    }

    private ForLoop nextForLoop(DFANode barrier, Symbol symbol)
    {
        Statement barrierStatement = barrier.getData("stmt");
        Procedure top = IRTools.getAncestorOfType(barrierStatement, Procedure.class);
        CompoundStatement compoundStatement = top.getBody();
        DepthFirstIterator iter = new DepthFirstIterator(compoundStatement);

        /* Wind to the barrier statement */
        while (iter.hasNext())
        {
            Traversable t = iter.next();
            if (t instanceof AnnotationStatement)
            {
                AnnotationStatement annotationStatement = (AnnotationStatement) t;
                if (annotationStatement == barrierStatement)
                {
                    break;
                }
            }
        }

        if (!iter.hasNext())
            return null;

        // iter.pruneOn(ForLoop.class);
        while (iter.hasNext())
        {
            Traversable t = iter.next();
            if (t instanceof ForLoop)
            {
                if (IRTools.containsSymbol(t, symbol))
                {
                    return (ForLoop) t;
                }
            }
        }

        return null;  //TODO
    }

    private int partitionedDimension(Section defSection)
    {
        for (Section.ELEMENT element : defSection)
        {
            int i;
            for (i = 0; i < element.size(); i++)
            {
                Expression expression = element.get(i);
                DepthFirstIterator iter = new DepthFirstIterator(expression);
                while (iter.hasNext())
                {
                    Object obj = iter.next();
                    if (obj instanceof Identifier)
                    {
                        if (obj.toString().startsWith("ompd_lb"))
                        {
                            return i;
                        }
                    }
                }
            }
        }
        return -1;  //TODO
    }

    private List<Section> previousDefSection(DFANode barrier, Symbol symbol)
    {
        List<Section> result = new ArrayList<Section>();
        Set<DFANode> visited = new HashSet<DFANode>();

        findPrevDefSectionRecursively(barrier, visited, symbol, result);

        if (result.isEmpty())
        {
            return null;
        }
        else
        {
            return result;
        }
    }

    private void findPrevDefSectionRecursively(DFANode node, Set<DFANode> visited, Symbol symbol, List<Section> result)
    {
        if (visited.contains(node))
        {
            return;
        }

        visited.add(node);

        if (OMPDTools.isBarrierNodeButNotFromSerialToParallel(node))
        {
            Section.MAP defSectionMap = node.getData("must_def_in");
            Section defSection = defSectionMap.get(symbol);
            if (defSection != null && !defSection.isEmpty())
            {
                result.add(defSection);
                return;
            }
        }

        /* find DefSections in predecessor nodes */
        for (DFANode pred : node.getPreds())
        {
            findPrevDefSectionRecursively(pred, visited, symbol, result);
        }
    }

    private boolean checkOneToOneMapping(DFANode barrier, Symbol symbol)
    {
        return false;  //TODO
    }

    private boolean checkAccessInLoop(DFANode barrier, Symbol symbol)
    {
        return false;  //TODO
    }

    private boolean checkSingleAccess(DFANode barrier, Symbol symbol)
    {
        return false;  //TODO
    }
}