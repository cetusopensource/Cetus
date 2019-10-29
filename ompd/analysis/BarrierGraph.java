package ompd.analysis;

import cetus.analysis.DFAGraph;
import cetus.analysis.DFANode;
import cetus.analysis.Section;
import cetus.exec.Driver;
import cetus.hir.*;
import ompd.hir.OMPDTools;
import ompd.hir.OmpdAnnotation;
import ompd.transforms.BoundRecord;

import javax.tools.Tool;
import java.util.*;

import static cetus.hir.PrintTools.println;

public class BarrierGraph extends DFAGraph
{
    // The symbol we are interested in.
    protected Symbol my_symbol;

    // CFG ID given by the collection of BarrierGraph
    protected int cfg_id;

    // Class that is marked as super nodes
    protected Class super_node;

    // Object that a CFG is created from (top-level call).
    protected Traversable root_node;

    protected TranslationUnit tu;

    private HashMap<Traversable, Boolean> barrierMap;

    private int verbosity = 5;

    /**
     * Constructs a BarrierGraph object with the given traversable object for the given symbol.
     * The entry node contains a string "ENTRY" for the key "stmt".
     *
     * @param t  the traversable object.
     * @param s  the symbol we are interested in.
     * @param id id given by BarrierGraphCollection
     */
    public BarrierGraph(Traversable t, Symbol s, int id)
    {
        this(t, s, id, null);
    }

    String getSymbolName()
    {
        return my_symbol.getSymbolName();
    }

    public BarrierGraph(Traversable t, Symbol s, int id, Class supernode)
    {
        super();

        if (Driver.getOptionValue("verbosity") != null)
            verbosity = Integer.valueOf(Driver.getOptionValue("verbosity")).intValue();

        root_node = t;
        super_node = supernode;
        my_symbol = s;
        cfg_id = id;
        barrierMap = new HashMap<Traversable, Boolean>();
        tu = IRTools.getAncestorOfType(root_node, TranslationUnit.class);
        if (tu == null)
            throw new IllegalArgumentException();

        markOwnershipOfBarrier(t);

        // ENTRY insertion.
        // TODO: determine whether we really need this entry node.
        //        DFANode entry = new DFANode("stmt", "ENTRY");
        //        entry.putData("tag", "FLOW ENTRY");
        //        addNode(entry);

        // Build and absorb.
        DFAGraph g = buildGraph(t);
        //        addEdge(entry, g.getFirst());

        absorb(g);

        // Optimize.
        reduce();
    }

    private void markOwnershipOfBarrier(Traversable t)
    {
        PrintTools.println("markOwnershipOfBarrier()", 5);
        if (hasBarrier(t))
            barrierMap.put(t, true);
        else
            barrierMap.put(t, false);
    }

    /**
     * It goes into the given IR tree recursively to check whether the tree
     * has a barrier annotation in the sub-tree. It also records the result
     * if a tree node is a statement for the fast lookup later.
     *
     * @param t root of the tree
     * @return true if the tree has a barrier annotation, otherwise false.
     */
    private boolean hasBarrier(Traversable t)
    {
        boolean result = false;

        if (t == null)
            return false;

        if (t instanceof AnnotationStatement && isBarrierAnnotation((AnnotationStatement) t))
        {
            barrierMap.put(t, true);
            return true;
        }

        List list = t.getChildren();
        if (list == null)
            return false;

        for (Object child : list)
        {
            if (child == null)
                continue;

            if (hasBarrier((Traversable) child))
            {
                result = true;
                if (child instanceof Statement)
                    barrierMap.put((Statement) child, true);
            }
            else
            {
                if (child instanceof Statement)
                    barrierMap.put((Statement) child, false);
            }

        }
        return result;
    }

    private boolean isBarrierAnnotation(AnnotationStatement stmt)
    {
        OmpdAnnotation annotation = stmt.getAnnotation(OmpdAnnotation.class, "barrier");
        if (annotation != null)
        {
            if (annotation.get("barrier") != "S2P")
            {
                Section.MAP local_def = (Section.MAP) annotation.get("local_def");
                if (local_def != null && local_def.containsKey(my_symbol))
                {
                    return true;
                }
                Section.MAP local_use = (Section.MAP) annotation.get("local_use");
                if (local_use != null && local_use.containsKey(my_symbol))
                {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Builds a control flow graph for a traversable object.
     *
     * @param t Traversable which we are constructing a DFAGraph for.
     * @return DFAGraph built from the Traversable t
     */
    protected DFAGraph buildGraph(Traversable t)
    {
        // TODO:
        DFAGraph ret = new DFAGraph();

        //PrintTools.println("buildGraph()", 5);
        if (!barrierMap.get(t))
        {
            //PrintTools.println("  tree doesn't have a barrier in it", 5);
            return ret;
        }

        if (t instanceof ForLoop)
            ret = buildForLoop((ForLoop) t);

        else if (t instanceof DoLoop)
            ret = buildDoLoop((DoLoop) t);

        else if (t instanceof Procedure)
            ret = buildProcedure((Procedure) t);

        else if (t instanceof CompoundStatement)
            ret = buildCompound((CompoundStatement) t);

        else if (t instanceof IfStatement)
            ret = buildIf((IfStatement) t);

        else if (t instanceof SwitchStatement)
            ret = buildSwitch((SwitchStatement) t);

        else if (t instanceof WhileLoop)
            ret = buildWhile((WhileLoop) t);

        else if (t instanceof AnnotationStatement)
            ret = buildAnnotationStatement((AnnotationStatement) t);
        else
        {
            PrintTools.println("BarrierGraph.buildGraph(): Not supported type = " + t, 0);
        }
        //		else if ( t instanceof AnnotationStatementRC )
        //			ret = buildAnnotationStatementRC((AnnotationStatementRC)t);
        //
        //        else if (t instanceof DeclarationStatement)
        //            ret = buildDeclarationStatement((DeclarationStatement) t);
        //
        //        else if (t instanceof BreakStatement) {
        //            ret = new DFAGraph();
        //            ret.addNode(buildBreak((Statement) t));
        //        } else if (t instanceof Case || t instanceof Default) {
        //            ret = new DFAGraph();
        //            ret.addNode(buildCase((Statement) t));
        //        } else if (t instanceof ContinueStatement) {
        //            ret = new DFAGraph();
        //            ret.addNode(buildContinue((Statement) t));
        //        } else if (t instanceof GotoStatement) {
        //            ret = new DFAGraph();
        //            ret.addNode(buildGoto((GotoStatement) t));
        //        } else if (t instanceof Label) {
        //            ret = new DFAGraph();
        //            ret.addNode(buildLabel((Label) t));
        //        } else {
        //            DFANode node = new DFANode("stmt", t);
        //            node.putData("ir", t);
        //            ret = new DFAGraph();
        //            ret.addNode(node);
        //        }
        //
        //        if (t != null && t != root_node && super_node != null &&
        //                super_node.isAssignableFrom(t.getClass())) {
        //            DFANode entry = new DFANode("super-entry", t);
        //            entry.putData("tag", t.getClass().getName());
        //            DFANode exit = new DFANode("super-exit", t);
        //            ret = new DFAGraph();
        //            ret.nodes.add(0, entry);
        //            ret.nodes.add(exit);
        //            ret.addEdge(entry, exit);
        //        }

        return ret;
    }

    //    private DFANode buildLabel(Label label) {
    //        return null;  // TODO: Implementation
    //    }
    //
    //    private DFANode buildGoto(GotoStatement gotoStatement) {
    //        return null;  // TODO: Implementation
    //    }
    //
    //    private DFANode buildContinue(Statement statement) {
    //        return null;  // TODO: Implementation
    //    }
    //
    //    private DFANode buildCase(Statement statement) {
    //        return null;  // TODO: Implementation
    //    }
    //
    //    private DFANode buildBreak(Statement statement) {
    //        return null;  // TODO: Implementation
    //    }

    private DFAGraph buildWhile(WhileLoop whileLoop)
    {
        // TODO: implementation needed
        return new DFAGraph();
    }

    private DFAGraph buildSwitch(SwitchStatement switchStatement)
    {
        // TODO: implementation needed
        return new DFAGraph();
    }

    private DFAGraph buildIf(IfStatement ifStatement)
    {
        // TODO: implementation needed
        return new DFAGraph();
    }

    private DFAGraph buildForLoop(ForLoop forLoop)
    {
        DFAGraph ret = new DFAGraph();

        PrintTools.println("buildForLoop", 5);
        if (!barrierMap.get(forLoop))
            return ret;

        //        DFANode enter = new DFANode("dummy", "merge-me");
        //        DFANode exit = new DFANode("dummy", "merge-me");

        CompoundStatement bs = (CompoundStatement) forLoop.getBody();
        DFAGraph body = buildGraph(bs);
        assert body != null;

        ret.absorb(body);
        try
        {
            ret.addEdge(body.getLast(), body.getFirst());
        }
        catch (ArrayIndexOutOfBoundsException e)
        {
            PrintTools.println("OutOfBoundsException!\n" + forLoop, 0);
            Tools.exit("Aborted.");
        }

        //        ret.addEdge(enter, body.getFirst());
        //        ret.absorb(body);
        //        ret.addEdge(body.getLast(), exit);
        //        ret.addEdge(exit, enter);

        return ret;
    }

    private DFAGraph buildDoLoop(DoLoop doLoop)
    {
        // TODO: implementation needed
        return new DFAGraph();
    }

    private DFAGraph buildDeclarationStatement(DeclarationStatement declarationStatement)
    {
        // TODO: implementation needed
        return new DFAGraph();
    }

    protected DFAGraph buildAnnotationStatement(AnnotationStatement stmt)
    {
        DFAGraph ret = new DFAGraph();

        OmpdAnnotation annotation = stmt.getAnnotation(OmpdAnnotation.class, "barrier");
        if (annotation != null)
        {
            DFANode node = new DFANode();
            node.putData("tag", "barrier");
            node.putData("barrier", annotation.get("barrier"));
            node.putData("stmt", stmt);

            /* invariant information is not needed because we already
             * know the place to put section code */
            Section.MAP ldef_map = annotation.get("local_def");
            if (ldef_map != null)
            {
                node.putData("ldef_section", ldef_map.get(my_symbol));
            }

            Section.MAP luse_map = annotation.get("local_use");
            if (luse_map != null)
            {
                node.putData("luse_section", luse_map.get(my_symbol));
            }

            Section.MAP guse_map = annotation.get("global_use");
            if (guse_map != null)
            {
                node.putData("guse_section", guse_map.get(my_symbol));
            }

            node.putData("barrier_id", annotation.get("barrier_id"));
            ret.addNode(node);
            PrintTools.println("buildAnnotationStatement() for barrier : " + ret, 5);
        }

        return ret;
    }

    // Check if the node contains unconditional jump instruction.

    protected static boolean isJump(DFANode node)
    {
        Object ir = node.getData("ir");
        return (ir != null && (ir instanceof BreakStatement ||
                ir instanceof ContinueStatement ||
                ir instanceof GotoStatement ||
                ir instanceof ReturnStatement));
    }

    private DFAGraph buildCompound(CompoundStatement compoundStatement)
    {
        DFAGraph ret = new DFAGraph();

        if (!barrierMap.get(compoundStatement))
            return ret;

        FlatIterator iterator = new FlatIterator(compoundStatement);

        PrintTools.println("buildCompound()", 5);

        // Absorbs sub-graph from each child.
        while (iterator.hasNext())
        {
            Traversable t = iterator.next();
            // Tools.println("Traversable = " + t + ", class = " + t.getClass(), 0);
            DFAGraph curr = buildGraph(t);

            // Jumps are not connected to the next statement.
            if (!ret.isEmpty() && !curr.isEmpty() && !isJump(ret.getLast()))
                ret.addEdge(ret.getLast(), curr.getFirst());

            ret.absorb(curr);
        }

        //        // Insert an empty node if this compound statement has no children.
        //        if (ret.size() == 0)
        //            ret.addNode(new DFANode("ir", new NullStatement()));
        //

        //        // Record live period of symbols by adding pointer to the symbol table
        //        if (!compoundStatement.getTable().isEmpty()) {
        //            ret.getFirst().putData("symbol-entry", compoundStatement);
        //            List symbol_exits = new ArrayList();
        //            symbol_exits.add(compoundStatement);
        //            ret.getLast().putData("symbol-exit", symbol_exits);
        //        }

        return ret;
    }

    protected DFAGraph buildProcedure(Procedure procedure)
    {
        PrintTools.println("buildProcedure(): " + procedure.getSymbolName(), 5);
        return buildGraph(procedure.getBody());
    }

    /**
     * Reduce graph by removing nodes with empty IR.
     */
    protected void reduce()
    {
        // TODO:
    }

    private Statement genNodeUpdateFunctionStatement(DFANode node, String function_name, Section section, int comm_id)
    {
        FunctionCall fc = new FunctionCall(new NameID(function_name));
        fc.addArgument(new IntegerLiteral(comm_id));
        /* TODO: NameID should be replaced by predefined symbols. */
        fc.addArgument(new NameID("ompd_i"));
        fc.addArgument(new IntegerLiteral(cfg_id));
        fc.addArgument(new IntegerLiteral(nodes.indexOf(node)));
        fc.addArgument(new NameID(my_symbol.getSymbolName()));
        fc.addArgument(new IntegerLiteral(section.size()));

        for (Section.ELEMENT elem : section)
        {
            for (Expression expression : elem)
            {
                if (expression instanceof RangeExpression)
                {
                    RangeExpression re = (RangeExpression) expression;
                    fc.addArgument(re.getLB().clone());
                    fc.addArgument(re.getUB().clone());
                }
                else
                {
                    fc.addArgument(expression.clone());
                    fc.addArgument(expression.clone());
                }
            }
        }

        return new ExpressionStatement(fc);
    }

    public void genNodeUpdateFunctionCalls(PrevDefsFinder finder)
    {
        for (DFANode node : nodes)
        {
            String tag = (String) node.getData("tag");
            if (tag != null && tag.equals("barrier"))
            {
                
                /* This for loop means the enclosing ompd_i loop that might be
                 * hoisted up to the outside of the outermost serial loop.
                 */
                assert node.getData("barrier_id") != null;
                Integer comm_id = (Integer) node.getData("barrier_id");
                Statement barrierStatement = node.getData("stmt");
                if (barrierStatement == null)
                    throw new IllegalAccessError();

                // DEF if exists
                Section ldef = node.getData("ldef_section");
                if (ldef != null)
                {
                    Set<Symbol> wanted = OMPDTools.getUseSymbols(ldef);
                    Set<Statement> positions = getInsertionPointForUpdateFunction(finder, barrierStatement, wanted);
                    Statement statement = genNodeUpdateFunctionStatement(node, "update_def", ldef, comm_id);
                    insertUpdateCode(positions, statement);
                }


                // USE if exists
                Section luse = node.getData("luse_section");
                if (luse != null)
                {
                    Set<Symbol> wanted = OMPDTools.getUseSymbols(luse);
                    Set<Statement> positions = getInsertionPointForUpdateFunction(finder, barrierStatement, wanted);
                    Statement statement = genNodeUpdateFunctionStatement(node, "update_use", luse, comm_id);
                    insertUpdateCode(positions, statement);
                }
            }
        }
    }

    private Set<Statement> getInsertionPointForUpdateFunction(PrevDefsFinder finder, Statement barrierStatement, Set<Symbol> wanted)
    {
        Set<Statement> positions = finder.getInsertionPointAfterPrevDefs(barrierStatement, wanted);
        Set<Statement> result = new HashSet<Statement>();

        /* check if a position is in a loop partitioning code, and if so, return the loop instead of the position. */
        for (Statement position : positions)
        {
            ForLoop boundInitLoop = getBoundInitLoop(position);
            if (boundInitLoop == null)
                result.add(position);
            else
                result.add(boundInitLoop);
        }

        return result;
    }

    private ForLoop getBoundInitLoop(Statement position)
    {
        Traversable t = position;

        if (!(t instanceof ForLoop))
            t = IRTools.getAncestorOfType(t, ForLoop.class);

        while (t != null)
        {
            ForLoop forLoop = (ForLoop) t;
            if (forLoop.getAnnotation(OmpdAnnotation.class, "bound_init_loop") != null)
                return forLoop;

            t = IRTools.getAncestorOfType(t, ForLoop.class);
        }

        return null;
    }

    private void insertUpdateCode(Set<Statement> positions, Statement statement)
    {
        for (Statement position : positions)
        {
            insertUpdateCode(position, statement);
        }
    }

    private void insertUpdateCode(Statement position, Statement statement)
    {
        ForLoop forLoop = OMPDTools.getDefUseUpdateLoopOrCreate(tu, position);
        CompoundStatement compoundStatement = (CompoundStatement) forLoop.getBody();
        compoundStatement.addStatement(statement.clone());
    }

    public void genCodeForCFG(Procedure procedure)
    {
        // TODO: Implementation
        CompoundStatement cStatement = procedure.getBody();

        List specs = my_symbol.getArraySpecifiers();
        ArraySpecifier spec = (ArraySpecifier) specs.get(0);  // Is it always correct?
        int numDims = spec.getNumDimensions();

        /* add comment that will help understand the meanings of the arguments */
        CodeAnnotation ca = new CodeAnnotation("/* initcfg(CFGID, NUM_NODES, MPI_TYPE, ARRAY_NAME, DIMENSION, SIZE_DIM0, ...); */");
        AnnotationStatement as = new AnnotationStatement(ca);
        cStatement.addStatement(as);

        // generate code in the create_cfgs() : init_cfg(0, numNodes, numDims, ...each dimension size);
        {
            FunctionCall fc = new FunctionCall(new NameID("init_cfg"));
            fc.addArgument(new IntegerLiteral(cfg_id));
            fc.addArgument(new StringLiteral(my_symbol.getSymbolName()));
            fc.addArgument(new IntegerLiteral(nodes.size()));
            fc.addArgument(getMPIType(my_symbol));
            /* Can't use symbol here, because it may not be available in the global scope.
             * We know somehow our future is going to be, but the real address of the symbol
             * may not available from the beginning. */
            //fc.addArgument(new NameID(my_symbol.getSymbolName()));
            fc.addArgument(new IntegerLiteral(numDims));
            for (int i = 0; i < spec.getNumDimensions(); i++)
            {
                Expression expr = Symbolic.simplify(spec.getDimension(i).clone());
                fc.addArgument(expr);
            }

            ExpressionStatement eStatement = new ExpressionStatement(fc);


            cStatement.addStatement(eStatement);
        }

        // generate code in the create_cfgs() : decode_edges(0, edges0);
        {
            FunctionCall fc = new FunctionCall(new NameID("decode_edges"));
            fc.addArgument(new IntegerLiteral(cfg_id));
            fc.addArgument(new NameID("barrier_ids" + cfg_id));
            fc.addArgument(new NameID("preds" + cfg_id));
            fc.addArgument(new NameID("succs" + cfg_id));
            ExpressionStatement eStatement = new ExpressionStatement(fc);

            cStatement.addStatement(eStatement);
        }

        // generate code before the create_cfgs() : int barrier_ids0[] = { ... }
        {
            ArraySpecifier array_spec = new ArraySpecifier();
            NameID array_id = new NameID("barrier_ids" + cfg_id);
            Declarator array_declarator = new VariableDeclarator(array_id, array_spec);
            List<Expression> list = getBarrierList();
            Initializer initializer = new Initializer(list);
            array_declarator.setInitializer(initializer);
            // array_id.setSymbol((Symbol)array_declarator);
            Declaration array_declaration = new VariableDeclaration(Specifier.INT, array_declarator);
            TranslationUnit tUnit = (TranslationUnit) procedure.getParent();
            tUnit.addDeclarationBefore(procedure, array_declaration);
        }

        // generate code before the create_cfgs() : int preds0[] = { ... }
        {
            ArraySpecifier array_spec = new ArraySpecifier();
            NameID array_id = new NameID("preds" + cfg_id);
            Declarator array_declarator = new VariableDeclarator(array_id, array_spec);
            List<Expression> list = getPredList();
            Initializer initializer = new Initializer(list);
            array_declarator.setInitializer(initializer);
            // array_id.setSymbol((Symbol)array_declarator);
            Declaration array_declaration = new VariableDeclaration(Specifier.INT, array_declarator);
            TranslationUnit tUnit = (TranslationUnit) procedure.getParent();
            tUnit.addDeclarationBefore(procedure, array_declaration);
        }

        // generate code before the create_cfgs() : int edges0[] = { ... }
        {
            ArraySpecifier array_spec = new ArraySpecifier();
            NameID array_id = new NameID("succs" + cfg_id);
            Declarator array_declarator = new VariableDeclarator(array_id, array_spec);
            List<Expression> list = getSuccList();
            Initializer initializer = new Initializer(list);
            array_declarator.setInitializer(initializer);
            // array_id.setSymbol((Symbol)array_declarator);
            Declaration array_declaration = new VariableDeclaration(Specifier.INT, array_declarator);
            TranslationUnit tUnit = (TranslationUnit) procedure.getParent();
            tUnit.addDeclarationBefore(procedure, array_declaration);
        }

        // generate code before the create_cfgs() : int node_w_luse0[] = { ... }
        {
            ArraySpecifier array_spec = new ArraySpecifier();
            NameID array_id = new NameID("node_w_luse" + cfg_id);
            Declarator array_declarator = new VariableDeclarator(array_id, array_spec);
            List<Expression> list = getNodesWithLocalUSE();
            Initializer initializer = new Initializer(list);
            array_declarator.setInitializer(initializer);
            // array_id.setSymbol((Symbol)array_declarator);
            Declaration array_declaration = new VariableDeclaration(Specifier.INT, array_declarator);
            TranslationUnit tUnit = (TranslationUnit) procedure.getParent();
            tUnit.addDeclarationBefore(procedure, array_declaration);

            // generate code in the create_cfgs() : init_luse(0, node_w_luse0);
            FunctionCall fc = new FunctionCall(new NameID("init_luse"));
            fc.addArgument(new IntegerLiteral(cfg_id));
            String arrayName = "node_w_luse" + cfg_id;
            fc.addArgument(new NameID("node_w_luse" + cfg_id));
            fc.addArgument(new IntegerLiteral(list.size()));
            ExpressionStatement eStatement = new ExpressionStatement(fc);

            cStatement.addStatement(eStatement);

        }
    }

    /**
     * This function constructs a barrier list of Expression from nodes.
     *
     * @return a list of Expression which contains array initial values.
     */
    private List<Expression> getBarrierList()
    {
        List<Expression> result = new ArrayList<Expression>();

        for (int i = 0; i < nodes.size(); i++)
        {
            DFANode node = nodes.get(i);
            Integer barrier_id = node.getData("barrier_id");
            assert barrier_id != null;
            result.add(new IntegerLiteral(barrier_id));
        }

        return result;
    }

    /**
     * This function constructs a list of Expression from nodes.
     * For example, if the first DFANode in nodes has two predecessors, whose
     * indexes of nodes are 1 and 2, then the edges are 1 -> 0 and 2 -> 0
     * respectively. These edges are going to appear in the translated
     * source code as { 0, 2, 1, 2 } and this function's role is to generate
     * the list of Expression from the values for Initializer.
     * <p/>
     * More details of the encoded values:
     * 0: node's id
     * 2: number of successors
     * 1: predecessor id (1/2)
     * 2: predecessor id (2/2)
     *
     * @return a list of Expression which contains array initial values.
     */
    private List<Expression> getPredList()
    {
        List<Expression> result = new ArrayList<Expression>();

        for (int i = 0; i < nodes.size(); i++)
        {
            DFANode node = nodes.get(i);
            result.add(new IntegerLiteral(i));
            result.add(new IntegerLiteral(node.getPreds().size()));
            for (DFANode predecessor : node.getPreds())
            {
                result.add(new IntegerLiteral(nodes.indexOf(predecessor)));
            }
        }

        return result;
    }

    /**
     * This function constructs a list of Expression from nodes.
     * For example, if the first DFANode in nodes has two successors, whose
     * indexes of nodes are 1 and 2, then the edges are 0 -> 1 and 0 -> 2
     * respectively. These edges are going to appear in the translated
     * source code as { 0, 2, 1, 2 } and this function's role is to generate
     * the list of Expression from the values for Initializer.
     * <p/>
     * More details of the encoded values:
     * 0: node's id
     * 2: number of successors
     * 1: successor id (1/2)
     * 2: successor id (2/2)
     *
     * @return a list of Expression which contains array initial values.
     */
    private List<Expression> getSuccList()
    {
        List<Expression> result = new ArrayList<Expression>();

        for (int i = 0; i < nodes.size(); i++)
        {
            DFANode node = nodes.get(i);
            result.add(new IntegerLiteral(i));
            result.add(new IntegerLiteral(node.getSuccs().size()));
            for (DFANode successor : node.getSuccs())
            {
                result.add(new IntegerLiteral(nodes.indexOf(successor)));
            }
        }

        return result;
    }

    private int getNumOfSuccs()
    {
        int result = 0;

        for (DFANode node : nodes)
        {
            result += node.getSuccs().size();
        }

        return result;
    }

    private List<Expression> getNodesWithLocalUSE()
    {
        List<Expression> result = new ArrayList<Expression>();

        for (int i = 0; i < nodes.size(); i++)
        {
            DFANode node = nodes.get(i);
            Section local_use = node.getData("luse_section");
            if (local_use != null && !local_use.isEmpty())
            {
                result.add(new IntegerLiteral(i));
            }
        }

        return result;
    }

    /* TODO: Copied from CommAnalysis.java. Redundant! */
    private List<IDExpression> getDeclaredSymbols(VariableDeclaration decl)
    {
        int i;
        ArrayList<IDExpression> list = new ArrayList<IDExpression>();
        for (i = 0; i < decl.getNumDeclarators(); i++)
        {
            Declarator declarator;
            declarator = decl.getDeclarator(i);
            list.add(declarator.getID());
        }

        return list;
    }

    /* TODO: Copied from CommAnalysis.java. Redundant! */
    private List<Specifier> findTypedefSpecifiers(String str)
    {
        Program program = IRTools.getAncestorOfType(root_node, Program.class);
        DepthFirstIterator iter = new DepthFirstIterator(program);
        iter.pruneOn(VariableDeclaration.class);

        PrintTools.println("findTypedefSpecifiers(" + str + ")", 5);

        for (; ; )
        {
            try
            {
                VariableDeclaration decl = (VariableDeclaration) iter.next(VariableDeclaration.class);

                if (decl.isTypedef())
                {
                    List<Specifier> specs = decl.getSpecifiers();

                    // Dump the list
                    println(decl.toString(), 5);

                    List<IDExpression> symbolList = getDeclaredSymbols(decl);
                    for (IDExpression id : symbolList)
                        if (id.getName().equals(str))
                            return decl.getSpecifiers();
                }

            }
            catch (NoSuchElementException e)
            {
                println("->Not found", 5);
                return null;
            }
        }
    }

    /* TODO: Copied from CommAnalysis.java. Redundant! */
    private Identifier getMPIType(Symbol symbol)
    {
        List<Specifier> type_specs = symbol.getTypeSpecifiers();
        String id = type_specs.get(0).toString();

        for (; ; )
        {
            String type = null;
            boolean signed = false;

            for (Specifier spec : type_specs)
            {
                if (spec.toString().equals("signed"))
                {
                    signed = true;
                    break;
                }
            }

            for (Specifier spec : type_specs)
            {
                String spec_str = spec.toString();
                if (spec_str.equals("char"))
                {
                    type = signed ? "MPI_SIGNED_CHAR" : "MPI_UNSIGNED_CHAR";
                }
                else if (spec_str.equals("short"))
                {
                    type = signed ? "MPI_SHORT" : "MPI_UNSIGNED_SHORT";
                }
                else if (spec_str.equals("int"))
                {
                    type = signed ? "MPI_INT" : "MPI_UNSIGNED";
                }
                else if (spec_str.equals("long"))
                {
                    type = signed ? "MPI_LONG" : "MPI_UNSIGNED_LONG";
                }
                else if (spec_str.equals("float"))
                {
                    type = "MPI_FLOAT";
                }
                else if (spec_str.equals("double"))
                {
                    type = "MPI_DOUBLE";
                }
            }

            if (type != null)
                return SymbolTools.getOrphanID(type);

/* FOR DEBUGGING
            // Dump the list
            Iterator<Specifier> iter = type_specs.iterator();
            int index = 0;
            println("Unsupported type, printing specifiers", 2);
            if(Tools.isScalar(symbol))
                println("symbol is scalar", 2);
            else if(SymbolTools.isArray(symbol))
                println("symbol is array", 2);
            while (iter.hasNext()) {
                Specifier spec = iter.next();
                println("speclist[" + index++ + "]: " + spec.toString(), 2);
            }
*/
            try
            {
                // Get the original type of this user-defined type
                type_specs = findTypedefSpecifiers(id);
            }
            catch (NullPointerException e)
            {
                return null;
            }
        }
    }
}
