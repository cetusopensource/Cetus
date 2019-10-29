package ompd.transforms;

import ompd.analysis.PrevDefsFinder;
import ompd.hir.*;
import cetus.analysis.*;
import cetus.hir.*;

import java.util.*;


public class LoopPartition
{

    Program program;
    static int loop_cnt = 0;
    Statement first_non_decl_stmt; // a reference Statement to add a new Statement before
    Procedure init_function;

    static boolean isDataPartitioning = false;
 
    private Symbol procid_symbol, nprocs_symbol, loop_i_symbol;
    TranslationUnit tu;

    public static int getNewLoopId()
    {
        return loop_cnt++;
    }

    // TODO: instead of using a boolean variable, subclass it.
    public LoopPartition(Program prog, boolean isDataPartitioning)
    {
        program = prog;
        this.isDataPartitioning = isDataPartitioning;
    }

    public LoopPartition(Program prog)
    {
        program = prog;
        isDataPartitioning = false;
    }

    public String getPassName()
    {
        return "[LoopPartition]";
    }

    public void start()
    {
        for (Traversable t : program.getChildren())
        {
            if (!(t instanceof TranslationUnit))
            {
                continue;
            }
            tu = (TranslationUnit) t;

            PrintTools.println("Input file name = " + tu.getInputFilename(), 5);

            init_function = null;

            declareOmpdVariables(tu);

            DepthFirstIterator proc_iter = new DepthFirstIterator(tu);
            proc_iter.pruneOn(Procedure.class);
            Set<Procedure> proc_set = proc_iter.getSet(Procedure.class);

            loop_cnt = 0;
            for (Procedure proc : proc_set)
            {
                partitionLoopsInProcedure(proc);
            }
        }
    }

    // TODO: These three variables are singleton. Make a singleton class and put them in it.
    private void declareOmpdVariables(TranslationUnit tu)
    {
        NameID nprocs_id, procid_id, loop_i_id;

        // TODO: using a string directly is a bad idea
        nprocs_id = new NameID("ompd_nprocs");
        procid_id = new NameID("ompd_procid");
        loop_i_id = new NameID("ompd_i");

        VariableDeclarator nprocs_declarator = new VariableDeclarator(nprocs_id);
        nprocs_symbol = nprocs_declarator;
        Declaration nprocs_decl = new VariableDeclaration(Specifier.INT, nprocs_declarator);
        tu.addDeclarationFirst(nprocs_decl);

        VariableDeclarator procid_declarator = new VariableDeclarator(procid_id);
        procid_symbol = procid_declarator;
        Declaration procid_decl = new VariableDeclaration(Specifier.INT, procid_declarator);
        tu.addDeclarationFirst(procid_decl);

        VariableDeclarator loop_i_declarator = new VariableDeclarator(loop_i_id);
        loop_i_symbol = loop_i_declarator;
        Declaration loop_i_decl = new VariableDeclaration(Specifier.INT, loop_i_declarator);
        tu.addDeclarationFirst(loop_i_decl);
    }

    private void partitionLoopsInProcedure(Procedure proc)
    {
        // global variable
        first_non_decl_stmt = IRTools.getFirstNonDeclarationStatement(proc.getBody());

        List<OmpdAnnotation> annotationList = IRTools.collectPragmas(proc, OmpdAnnotation.class, "for");
        for (OmpdAnnotation annotation : annotationList)
        {
            ForLoop loop = (ForLoop) annotation.getAnnotatable();

            partitionLoop(proc, loop);
            // TODO: IsContiguousAccess is not working for BT and SP. Fix it.
            //            if (OMPDTools.IsContiguousAccess(proc, loop, range_map)) {
            //                partitionLoop(proc, loop, range_map);
            //            } else {
            //                PrintTools.println("Parallel ForLoop is serialized ", 2);
            //                annotation.remove("for");
            //                annotation.put("for_serialized", true);
            //            }
        }
    }

    public static Symbol getnprocsSymbol(TranslationUnit tu)
    {
        String str = "ompd_nprocs";
        return SymbolTools.getSymbolOfName(str, tu);
    }

    public static Symbol getiSymbol(TranslationUnit tu)
    {
        String str = "ompd_i";
        return SymbolTools.getSymbolOfName(str, tu);
    }

    /* Get the ompd bound loop. If the loop does not exist, then it will create one. */
    protected static ForLoop getBoundInitLoopOrCreate(TranslationUnit tu, Statement position)
    {
        ForLoop boundInitLoop;

        if (position.getAnnotation(OmpdAnnotation.class, OMPDSTR.BOUND_LOOP) == null)
        {

            ForLoop ompdLoop = OMPDTools.createOmpdLoop(tu);
            OMPDTimer.encloseByTimerCode(ompdLoop, OMPDTimer.BOUND_INIT);

            CompoundStatement compoundStatement = (CompoundStatement) position.getParent();
            compoundStatement.addStatementAfter(position, ompdLoop);

            OmpdAnnotation ompdAnnotation = new OmpdAnnotation();
            ompdAnnotation.put(OMPDSTR.BOUND_LOOP, ompdLoop);
            /* create bound record and attach it to the bound init loop */
            BoundRecord record = new BoundRecord();
            ompdAnnotation.put(OMPDSTR.BOUND_RECORD, record);

            position.annotate(ompdAnnotation);

            boundInitLoop = ompdLoop;

            /* Let's mark it as 'bound_init_loop' */
            boundInitLoop.annotate(new OmpdAnnotation("bound_init_loop", null));

        }
        else
        {
            OmpdAnnotation ompdAnnotation = position.getAnnotation(OmpdAnnotation.class, OMPDSTR.BOUND_LOOP);
            boundInitLoop = ompdAnnotation.get(OMPDSTR.BOUND_LOOP);
        }

        return boundInitLoop;
    }

    public void partitionLoop(Procedure proc, ForLoop loop)
    {
        PrintTools.println("[partitionLoop] strt " + loop_cnt + "-th parallel for loop", 2);
        PrintTools.println("--------------------", 2);
        PrintTools.println(loop.toString(), 2);
        PrintTools.println("--------------------", 2);

        /* check for a canonical loop */
        if (!LoopTools.isCanonical(loop))
        {
            PrintTools.println("[partitionLoop] loop is not canonical loop. Skipped.", 0);
            return;
        }

        /*
         * In many cases, omp for loops will have a same position to define the bounds, then
         * having one for loop will be better for appearance and for Range Analysis maybe
         */
        /*
         * get the original loop bound Expressions
         * note: do not move these codes after loops bounds are replaced with the new ones
         */
        Expression orig_lb = LoopTools.getLowerBoundExpression(loop);
        Expression orig_ub = LoopTools.getUpperBoundExpression(loop);

        // Statement position = OMPDTools.findPosition(proc, loop, orig_ub, orig_lb);
        Set<Symbol> useSymbols = new HashSet<Symbol>();
        useSymbols.addAll(DataFlowTools.getUseSymbol(orig_lb));
        useSymbols.addAll(DataFlowTools.getUseSymbol(orig_ub));
        PrevDefsFinder finder = new PrevDefsFinder(proc, null);
        Set<Statement> positions = finder.getInsertionPointAfterPrevDefs(loop, useSymbols);

        // find the ID registered previously in BOUND_RECORDs in the positions and use it if it exists.
        int loop_id = findLoopId(positions, orig_lb, orig_ub);
        if (loop_id != -1)
        {
            // reuse this loop id, just replace the loop's bound with LB and UB of this ID.
        }
        else
        {
            // allocate a new loop_id
            loop_id = getNewLoopId();
            createBoundInitLoop(tu, loop_id, positions, orig_lb, orig_ub);
        }

        /* replace the lower and upper bound expressions of the original loop. */
        replaceBounds(loop, loop_id);

        PrintTools.println("[partitionLoop] done", 2);
    }

    public static int findLoopId(Set<Statement> positions, Expression orig_lb, Expression orig_ub)
    {
        ArrayList<Statement> list = new ArrayList<Statement>(positions);
        assert positions.size() > 0;

        Statement position = list.get(0);
        BoundRecord record = getBoundRecord(position);
        if (record == null)
        {
            return -1;
        }

        int loopId = record.getLoopId(orig_lb, orig_ub);
        if (loopId == -1)
            return -1;

        for (int i = 1; i < list.size(); i++)
        {
            position = list.get(i);
            record = getBoundRecord(position);
            int id = record.getLoopId(orig_lb, orig_ub);
            if (id != loopId)
            {
                return -1;
            }
        }

        return loopId;
    }

    /**
     * It declares necessary variables identified by loop id, and
     * creates one bound init loop just after each position statement.
     *
     * @param tu        TranslationUnit
     * @param loopId    newly created bound init loop id
     * @param positions set of statements after which the bound loop will be inserted
     * @param orig_lb   original lb expression of the loop being partitioned
     * @param orig_ub   original ub expression of the loop being partitioned
     */
    public static void createBoundInitLoop(TranslationUnit tu, int loopId, Set<Statement> positions, Expression orig_lb, Expression orig_ub)
    {
        declareBoundVariables(tu, loopId);
        insertBoundInitCode(tu, positions, loopId, orig_lb, orig_ub);
    }

    protected static void insertBoundInitCode(TranslationUnit tu, Set<Statement> positions, int loopId, Expression orig_lb, Expression orig_ub)
    {
        for (Statement position : positions)
        {
            if (isDataPartitioning)
            {
                insertBoundInitCodeData(tu, position, loopId, orig_lb, orig_ub);
            }
            else
            {
                insertBoundInitCodeIter(tu, position, loopId, orig_lb, orig_ub);
            }
        }
    }

    /* This function is partitions iterations of the parallel loop.
     */
    protected static void insertBoundInitCodeIter(TranslationUnit tu, Statement position, int loopId, Expression orig_lb, Expression orig_ub)
    {
        PrintTools.println("Work Partitioning based on the iteration of the loop", 0);
        ForLoop ompd_i_loop = getBoundInitLoopOrCreate(tu, position);
        BoundRecord boundRecord = getBoundRecord(position);
        boundRecord.add(loopId, orig_lb, orig_ub);

        CompoundStatement loop_body = (CompoundStatement) ompd_i_loop.getBody();

        Symbol qSymbol, rSymbol, countSymbol, lbSymbol, ubSymbol, nprocsSymbol, iSymbol;
        qSymbol = OMPDTools.getqSymbol(tu, loopId);
        rSymbol = OMPDTools.getrSymbol(tu, loopId);
        countSymbol = OMPDTools.getcountSymbol(tu, loopId);
        lbSymbol = OMPDTools.getlbSymbol(tu, loopId);
        ubSymbol = OMPDTools.getubSymbol(tu, loopId);
        nprocsSymbol = getnprocsSymbol(tu);
        iSymbol = getiSymbol(tu);

        assert qSymbol != null && rSymbol != null && countSymbol != null && lbSymbol != null && ubSymbol != null;
        assert nprocsSymbol != null && iSymbol != null;

        /* insert following array initializations in the bound init loop */
        Expression span_expr = Symbolic.subtract(orig_ub.clone(), orig_lb.clone());
        span_expr = Symbolic.add(span_expr, new IntegerLiteral(1));

        /* ompd_q = span / ompd_nprocs; */
        {
            Expression quotient = Symbolic.divide(span_expr.clone(), new Identifier(nprocsSymbol));
            AssignmentExpression quotient_ae = new AssignmentExpression(new Identifier(qSymbol), AssignmentOperator.NORMAL, quotient);
            ExpressionStatement quotient_es = new ExpressionStatement(quotient_ae);
            loop_body.addStatement(quotient_es);
        }

        /* ompd_r = span % ompd_nprocs; */
        {
            Expression remainder = Symbolic.mod(span_expr.clone(), new Identifier(nprocsSymbol));
            AssignmentExpression remainder_ae = new AssignmentExpression(new Identifier(rSymbol), AssignmentOperator.NORMAL, remainder);
            ExpressionStatement remainder_es = new ExpressionStatement(remainder_ae);
            loop_body.addStatement(remainder_es);
        }

        /* if (ompd_i < ompd_remainder) {
               ompd_count0[ompd_i] = ompd_quotient + 1;
           } else {
               ompd_count0[ompd_i] = ompd_quotient;
           }
        */
        {
            IfStatement ifStatement;
            Expression ifCondition, lhs, rhs, trueExpression, falseExpression;
            Statement trueStatement, falseStatement;

            ifCondition = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.COMPARE_LT, new Identifier(rSymbol));

            /* true statement */
            lhs = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(new Identifier(qSymbol), BinaryOperator.ADD, new IntegerLiteral(1));
            trueExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            trueStatement = new ExpressionStatement(trueExpression);

            /* false statement */
            lhs = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new Identifier(qSymbol);
            falseExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            falseStatement = new ExpressionStatement(falseExpression);

            ifStatement = new IfStatement(ifCondition, trueStatement, falseStatement);
            loop_body.addStatement(ifStatement);
        }

        /* if (ompd_i == 0) {
               ompd_lb0[ompd_i] = original_lb;
           } else {
               ompd_lb0[ompd_i] = ompd_ub0[ompd_i-1] + 1;
           }
        */
        {
            IfStatement ifStatement;
            Expression ifCondition, lhs, rhs, trueExpression, falseExpression;
            Statement trueStatement, falseStatement;

            ifCondition = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.COMPARE_EQ, new IntegerLiteral(0));

            /* true statement */
            lhs = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs = orig_lb.clone();
            trueExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            trueStatement = new ExpressionStatement(trueExpression);

            /* false statement */
            lhs = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.SUBTRACT, new IntegerLiteral(1));
            rhs = new ArrayAccess(new Identifier(ubSymbol), rhs);
            rhs = new BinaryExpression(rhs, BinaryOperator.ADD, new IntegerLiteral(1));
            falseExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            falseStatement = new ExpressionStatement(falseExpression);

            ifStatement = new IfStatement(ifCondition, trueStatement, falseStatement);
            loop_body.addStatement(ifStatement);
        }

        /* ompd_ub0[ompd_i] = ompd_lb0[ompd_i] + ompd_count0[ompd_i] - 1; */
        {
            Expression lhs, rhs1, rhs2, rhs, expression;
            Statement statement;

            lhs = new ArrayAccess(new Identifier(ubSymbol), new Identifier(iSymbol));
            rhs1 = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs2 = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(rhs1, BinaryOperator.ADD, rhs2);
            rhs = new BinaryExpression(rhs, BinaryOperator.SUBTRACT, new IntegerLiteral(1));
            expression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            statement = new ExpressionStatement(expression);
            loop_body.addStatement(statement);
        }

    }

    /* This function is partitions iterations of the parallel loop based on the rank of the dimension.
     */
    protected static void insertBoundInitCodeData(TranslationUnit tu, Statement position, int loopId, Expression orig_lb, Expression orig_ub)
    {
        PrintTools.println("Work Partitioning based on the rank of the array", 0);
        ForLoop ompd_i_loop = getBoundInitLoopOrCreate(tu, position);
        BoundRecord boundRecord = getBoundRecord(position);
        boundRecord.add(loopId, orig_lb, orig_ub);

        CompoundStatement loop_body = (CompoundStatement) ompd_i_loop.getBody();

        Symbol qSymbol, rSymbol, countSymbol, lbSymbol, ubSymbol, nprocsSymbol, iSymbol;
        qSymbol = OMPDTools.getqSymbol(tu, loopId);
        rSymbol = OMPDTools.getrSymbol(tu, loopId);
        countSymbol = OMPDTools.getcountSymbol(tu, loopId);
        lbSymbol = OMPDTools.getlbSymbol(tu, loopId);
        ubSymbol = OMPDTools.getubSymbol(tu, loopId);
        nprocsSymbol = getnprocsSymbol(tu);
        iSymbol = getiSymbol(tu);

        assert qSymbol != null && rSymbol != null && countSymbol != null && lbSymbol != null && ubSymbol != null;
        assert nprocsSymbol != null && iSymbol != null;

        /* insert following array initializations in the bound init loop */
        Expression span_expr = Symbolic.subtract(orig_ub.clone(), orig_lb.clone());
        span_expr = Symbolic.add(span_expr, new IntegerLiteral(1));

        /* ompd_q = span / ompd_nprocs; */
        {
            Expression quotient = Symbolic.divide(span_expr.clone(), new Identifier(nprocsSymbol));
            AssignmentExpression quotient_ae = new AssignmentExpression(new Identifier(qSymbol), AssignmentOperator.NORMAL, quotient);
            ExpressionStatement quotient_es = new ExpressionStatement(quotient_ae);
            loop_body.addStatement(quotient_es);
        }

        /* ompd_r = span % ompd_nprocs; */
        {
            Expression remainder = Symbolic.mod(span_expr.clone(), new Identifier(nprocsSymbol));
            AssignmentExpression remainder_ae = new AssignmentExpression(new Identifier(rSymbol), AssignmentOperator.NORMAL, remainder);
            ExpressionStatement remainder_es = new ExpressionStatement(remainder_ae);
            loop_body.addStatement(remainder_es);
        }

        /* if (ompd_i < ompd_remainder) {
               ompd_count0[ompd_i] = ompd_quotient + 1;
           } else {
               ompd_count0[ompd_i] = ompd_quotient;
           }
        */
        {
            IfStatement ifStatement;
            Expression ifCondition, lhs, rhs, trueExpression, falseExpression;
            Statement trueStatement, falseStatement;

            ifCondition = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.COMPARE_LT, new Identifier(rSymbol));

            /* true statement */
            lhs = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(new Identifier(qSymbol), BinaryOperator.ADD, new IntegerLiteral(1));
            trueExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            trueStatement = new ExpressionStatement(trueExpression);

            /* false statement */
            lhs = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new Identifier(qSymbol);
            falseExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            falseStatement = new ExpressionStatement(falseExpression);

            ifStatement = new IfStatement(ifCondition, trueStatement, falseStatement);
            loop_body.addStatement(ifStatement);
        }

        /* if (ompd_i == 0) {
               ompd_lb0[ompd_i] = original_lb;
           } else {
               ompd_lb0[ompd_i] = ompd_ub0[ompd_i-1] + 1;
           }
        */
        {
            IfStatement ifStatement;
            Expression ifCondition, lhs, rhs, trueExpression, falseExpression;
            Statement trueStatement, falseStatement;

            ifCondition = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.COMPARE_EQ, new IntegerLiteral(0));

            /* true statement */
            lhs = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs = orig_lb.clone();
            trueExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            trueStatement = new ExpressionStatement(trueExpression);

            /* false statement */
            lhs = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(new Identifier(iSymbol), BinaryOperator.SUBTRACT, new IntegerLiteral(1));
            rhs = new ArrayAccess(new Identifier(ubSymbol), rhs);
            rhs = new BinaryExpression(rhs, BinaryOperator.ADD, new IntegerLiteral(1));
            falseExpression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            falseStatement = new ExpressionStatement(falseExpression);

            ifStatement = new IfStatement(ifCondition, trueStatement, falseStatement);
            loop_body.addStatement(ifStatement);
        }

        /* ompd_ub0[ompd_i] = ompd_lb0[ompd_i] + ompd_count0[ompd_i] - 1; */
        {
            Expression lhs, rhs1, rhs2, rhs, expression;
            Statement statement;

            lhs = new ArrayAccess(new Identifier(ubSymbol), new Identifier(iSymbol));
            rhs1 = new ArrayAccess(new Identifier(lbSymbol), new Identifier(iSymbol));
            rhs2 = new ArrayAccess(new Identifier(countSymbol), new Identifier(iSymbol));
            rhs = new BinaryExpression(rhs1, BinaryOperator.ADD, rhs2);
            rhs = new BinaryExpression(rhs, BinaryOperator.SUBTRACT, new IntegerLiteral(1));
            expression = new AssignmentExpression(lhs, AssignmentOperator.NORMAL, rhs);
            statement = new ExpressionStatement(expression);
            loop_body.addStatement(statement);
        }

    }

    protected static BoundRecord getBoundRecord(Statement position)
    {
        OmpdAnnotation ompdAnnotation = position.getAnnotation(OmpdAnnotation.class, OMPDSTR.BOUND_RECORD);
        if (ompdAnnotation == null)
        {
            return null;
        }

        return ompdAnnotation.get(OMPDSTR.BOUND_RECORD);
    }

    /*
     * Declare lb, ub, and chunk in the translation unit.
     * int ompd_lb#count[NPROCS];
     * int ompd_ub#count[NPROCS];
     * int ompd_chunk#count;
     */
    public static void declareBoundVariables(TranslationUnit tu, int loopId)
    {
        ArraySpecifier array_spec = new ArraySpecifier(SymbolTools.getOrphanID("NPROCS"));

        NameID lb_array_id = new NameID("ompd_lb" + loopId);
        VariableDeclarator lb_array_declarator = new VariableDeclarator(lb_array_id, array_spec);
        Declaration lb_array_decl = new VariableDeclaration(Specifier.INT, lb_array_declarator);
        tu.addDeclarationFirst(lb_array_decl);

        NameID ub_array_id = new NameID("ompd_ub" + loopId);
        VariableDeclarator ub_array_declarator = new VariableDeclarator(ub_array_id, array_spec);
        Declaration ub_array_decl = new VariableDeclaration(Specifier.INT, ub_array_declarator);
        tu.addDeclarationFirst(ub_array_decl);

        NameID count_array_id = new NameID("ompd_count" + loopId);
        VariableDeclarator count_array_declarator = new VariableDeclarator(count_array_id, array_spec);
        Declaration count_array_decl = new VariableDeclaration(Specifier.INT, count_array_declarator);
        tu.addDeclarationFirst(count_array_decl);

        NameID q_id = new NameID("ompd_quotient" + loopId);
        VariableDeclarator q_declarator = new VariableDeclarator(q_id);
        Declaration q_decl = new VariableDeclaration(Specifier.INT, q_declarator);
        tu.addDeclarationFirst(q_decl);

        NameID r_id = new NameID("ompd_remainder" + loopId);
        VariableDeclarator r_declarator = new VariableDeclarator(r_id);
        Declaration r_decl = new VariableDeclaration(Specifier.INT, r_declarator);
        tu.addDeclarationFirst(r_decl);
    }

    private void replaceBounds(ForLoop loop, int loopId)
    {
        /* make a backup for the loop initialization and condition. */
        {
            OmpdAnnotation annotation = loop.getAnnotation(OmpdAnnotation.class, "for");
            assert annotation != null;
            annotation.put("origInitStmt", loop.getInitialStatement().clone());
            annotation.put("origCondExpr", loop.getCondition().clone());
        }

        /* identify the loop index variable */
        Expression ivar = LoopTools.getIndexVariable(loop);

        Symbol lbSymbol = OMPDTools.getlbSymbol(tu, loopId);
        Symbol ubSymbol = OMPDTools.getubSymbol(tu, loopId);

        /* Parallel loop modifications from here */
        ArrayAccess lb_array, ub_array;
        lb_array = new ArrayAccess(new Identifier(lbSymbol), new Identifier(procid_symbol));
        ub_array = new ArrayAccess(new Identifier(ubSymbol), new Identifier(procid_symbol));

        /*
        * modify initial expression of the loop : i = lb;  --> i = new_lb;
        */

        ExpressionStatement init_stmt = (ExpressionStatement) loop.getInitialStatement();
        Expression init_rhse = ((BinaryExpression) init_stmt.getExpression()).getRHS();
        init_rhse.swapWith(lb_array);

        /*
        * modify condition expression of the loop : i op ub; --> i <= new_ub
        */
        BinaryExpression new_cond_expr = new BinaryExpression(ivar.clone(), BinaryOperator.COMPARE_LE, ub_array);
        loop.setCondition(new_cond_expr);

    }

    private ForLoop findForLoop(Procedure proc)
    {
        DepthFirstIterator iter = new DepthFirstIterator(proc);
        while (iter.hasNext())
        {
            Object obj = iter.next();
            if (obj instanceof ForLoop)
            {
                return (ForLoop) obj;
            }
        }
        Tools.exit("No ForLoop in ompd_init_loop_bounds function");
        return null;
    }
}