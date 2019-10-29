package ompd.analysis;

import ompd.hir.*;

import java.io.*;
import java.lang.reflect.Method;
import java.util.*;

import cetus.analysis.*;
import cetus.hir.*;
import cetus.exec.*;

ysisForOMPD extends AnalysisPass {
    private int debug_level;
    private int debug_tab;

    /**
     * Useful for passing to setPrintMethod or setClassPrintMethod.
     * Specially this is useful to print omp threadprivate pragma, which
     * can exist as a Declaration, not wrapped by AnnotationStatement,
     * in a TranslationUnit.
     */
    public static final Method print_as_omppragma_method;

    static {
        Class[] params = new Class[2];

        try {
            params[0] = OmpAnnotation.class;
            params[1] = OutputStream.class;
            print_as_omppragma_method = OmpAnalysisForOMPD.class.getMethod("printAsOmpPragma", params);
        } catch (NoSuchMethodException e) {
            throw new InternalError();
        }
    }

    public OmpAnalysisForOMPD(Program program) {
        super(program);
        debug_level = Integer.valueOf(Driver.getOptionValue("verbosity")).intValue();
        debug_tab = 0;
    }

    public String getPassName() {
        return new String("[OmpAnalysisForOMPD]");
    }

    private OmpdAnnotation toOmpdAnnotation(OmpAnnotation ompAnnotation) {
        OmpdAnnotation ompdAnnotation = new OmpdAnnotation();
        Set<String> keySet = ompAnnotation.keySet();
        for (String key : keySet) {
            ompdAnnotation.put(key, ompAnnotation.get(key));
        }
        return ompdAnnotation;
    }

    private void copyOmp2OmpdAnnotation() {
        List<OmpAnnotation> ompAnnotationList = OMPDTools.collectPragmas(program, OmpAnnotation.class);
        for (OmpAnnotation ompAnnotation : ompAnnotationList) {
            OmpdAnnotation ompdAnnotation = toOmpdAnnotation(ompAnnotation);
            ompAnnotation.getAnnotatable().annotate(ompdAnnotation);
        }
    }

    public void start() {
        HashSet<String> threadprivate_set;
        
        /* Collect OpenMP threadprivate variables. */
        threadprivate_set = new HashSet<String>();
        List<OmpAnnotation> ThreadPrivateAnnots = IRTools.collectPragmas(program, OmpAnnotation.class, "threadprivate");
        for (OmpAnnotation tp_annot : ThreadPrivateAnnots) {
            threadprivate_set.addAll((HashSet<String>) tp_annot.get("threadprivate"));
        }

        /* generate cetus annotations from omp annotations. */
        copyOmp2OmpdAnnotation();

        /* put the collected threadprivate set to cetus annotations that have either "parallel" or "for". */
        List<OmpdAnnotation> ompdAnnotationList = OMPDTools.collectPragmas(program, OmpdAnnotation.class);
        for (OmpdAnnotation ompdAnnotation : ompdAnnotationList) {
            if (ompdAnnotation.containsKey("threadprivate")) {
                continue;
            } else if (ompdAnnotation.containsKey("parallel")) {
                ompdAnnotation.put("threadprivate", threadprivate_set);
            } else if (ompdAnnotation.containsKey("for")) {
                ompdAnnotation.put("threadprivate", threadprivate_set);
            }
        }

        /* debugging purpose */
        display();

        /*
         * OpenMP can express shared variables within a parallel region using shared
         * clause, but it is often the case that not all shared variables are listed
         * in shared cluase when default is shared
         * The shared_analysis method finds all shared variables used within
         * a parallel region inter-procedurally and provide that information in the
         * form of Annotation attached to the parallel region (structured block).
         */
        shared_analysis();

        /*
         * Convert a set of Strings in each OpenMP reduction clause into a set of Symbols.
         * - This method should be called right after OmpAnalysis.start() if your pass wants
         * to handle OpenMP reduction clauses.
         * - This method is not included in OmpAnalysis.start() because this method may modify
         * shared set information if reduction clauses include shared variables; if a shared variable
         * is used as a reduction variable, it should be removed from shared set.
         */
        //convertReductionClauses();
    }

    /**
     * shared_analysis
     * Limitations: the following two cases are not tested
     * - Heap-allocated variables are shared
     * - Formal arguments of called routines in the region that are passed by
     * reference inherit the data-sharing attributes of the associated actual argument.
     */
    public void shared_analysis() {
        PrintTools.println("shared_anlaysis strt", 5);

        List<OmpdAnnotation> ompdAnnotationList = IRTools.collectPragmas(program, OmpdAnnotation.class, "parallel");

        /*
         * There is only one AnnotationStatement for multiple lines of OpenMP pragmas
         * For example, a single AnnotationStatement will represent the following two
         * lines of omp pragmas.
         *    #pragma omp parallel
         *    #pragma omp for private(k)
         *    for (i=0; i<N; i++) { ... }
         */
        // shared variable analysis for every parallel region
        for (OmpdAnnotation ompdAnnotation : ompdAnnotationList) {
            HashSet<Symbol> SharedSet;
            Statement ownerStatement;

            ownerStatement = (Statement) ompdAnnotation.getAnnotatable();

            /*
             * PART I : gather phase
             * finds all shared variables within a parallel region inter-procedurally
             * include downward inter-procedural analysis
             */
            SharedSet = findSharedInRegion(ompdAnnotation, ownerStatement);

            if (ompdAnnotation.containsKey("shared")) {
                ompdAnnotation.remove("shared");
            }
            ompdAnnotation.put("shared", SharedSet);

            /*
             * PART II : distribution phase
             * the following while loop searches all parallel for-loops annotated
             * with "omp for" and find all shared variable for each for-loop
             */
            runIpaSharedInForLoop(ompdAnnotation, ownerStatement);

            /*
             * Handle copyin clause
             * FIXME: If threadprivate variable is accessed only in a function
             *        called in the parallel region, below conversion will omit it.
             */
            if (ompdAnnotation.containsKey("copyin")) {
                HashSet<String> tmp_set = ompdAnnotation.get("copyin");
                HashSet<Symbol> OmpCopyinSet = convertString2Symbol(tmp_set, ownerStatement);
                ompdAnnotation.remove("copyin");
                ompdAnnotation.put("copyin", OmpCopyinSet);
            }
        }

        PrintTools.println("shared_anlaysis done", 5);
    }

    /**
     * Finds all parallel for-loops (we also need to include critical sections, too) and
     * find shared variables within a for-loop and attach shared variables to the for-loop.
     *
     * @param par_map is an OpenMP annotation map for the parallel region
     * @param stmt    is a structured block for the parallel region - it can be
     *                either CompoundStatement or ForLoop
     */
    private void runIpaSharedInForLoop(HashMap par_map, Statement stmt) {
        PrintTools.println("[runIpaSharedInForLoop] strt", 5);
        DepthFirstIterator iter = new DepthFirstIterator(stmt);
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof OmpdAnnotation) {
                OmpdAnnotation ompdAnnotation = (OmpdAnnotation) obj;
                if (ompdAnnotation.containsKey("for")) {
                    ForLoop forLoop;

                    forLoop = (ForLoop) ompdAnnotation.getAnnotatable();
                    findSharedInForLoop(par_map, ompdAnnotation, forLoop);
                }
            } else if (obj instanceof FunctionCall) {
                FunctionCall call = (FunctionCall) obj;
                // called_procedure is null for system calls
                Procedure called_procedure = call.getProcedure();

                /*
                 * Seungjai: FIXME!
                 * If a shared varible in the par_map is passed to a function through parameter list,
                 * then we need to find a way to replace this shared varible in the par_map with the
                 * actual parameter in the called function.
                 */
                if (called_procedure != null) {
                    PrintTools.println("[runIpaSharedInForLoop] going down to proc: " + called_procedure.getName(), 5);
                    runIpaSharedInForLoop(par_map, called_procedure.getBody()); // recursive call
                }
            }
        }
        PrintTools.println("[runIpaSharedInForLoop] done", 5);
    }

    /**
     * attach AnnotationStatement for shared variable to the loop
     */
    private void findSharedInForLoop(HashMap par_map, HashMap for_map, ForLoop loop) {
        HashSet<String> tmp_set;

        // private variables annotated by "omp private" to the current for-loop
        tmp_set = (HashSet<String>) for_map.get("private");
        HashSet<Symbol> OmpPrivSet = convertString2Symbol(tmp_set, loop);
        displaySet("OmpPrivSet in a loop", OmpPrivSet);

        // threadprivate variables annotated by "omp threadprivate" to the current for-loop
        tmp_set = (HashSet<String>) for_map.get("threadprivate");
        HashSet<Symbol> OmpThreadPrivSet = convertString2Symbol(tmp_set, loop);
        displaySet("OmpThreadPrivSet in a loop", OmpThreadPrivSet);

        /*
           * "omp for" does not have shared clause, but for other analysis, we
           * keep shared set for each "omp for" loop
           */
        // shared variables annotated by "omp shared" to the current for-loop
        tmp_set = (HashSet<String>) for_map.get("shared");
        HashSet<Symbol> OmpSharedSet = convertString2Symbol(tmp_set, loop);
        displaySet("OmpSharedSet in a loop", OmpSharedSet);

        // shared variables found by shared_analysis to the enclosing parallel region
        Set<Symbol> ParSharedSet = (Set<Symbol>) par_map.get("shared");
        // private variables in the enclosing parallel region
        Set<Symbol> ParPrivateSet = (Set<Symbol>) par_map.get("private");

        // Put loop index variable into prvate set
        Expression ivar_expr = LoopTools.getIndexVariable(loop);
        Symbol ivar = SymbolTools.getSymbolOf(ivar_expr);
        OmpPrivSet.add(ivar);

        // all variables accessed within the current for-loop
        Set<Symbol> ForAccessedSet = SymbolTools.getAccessedSymbols(loop);

        // find private variables for the current for-loop
        for (Symbol symbol : ParPrivateSet) {
            if (ForAccessedSet.contains(symbol)) {
                OmpPrivSet.add(symbol);
            }
        }

        // find shared variables for the current for-loop
        Set<Symbol> ForSharedSet = new HashSet<Symbol>();
        for (Symbol symbol : ParSharedSet) {
            if (ForAccessedSet.contains(symbol)) {
                ForSharedSet.add(symbol);
            }
        }

        // Shared = Shared - OmpShared - OmpPriv
        ForSharedSet.addAll(OmpSharedSet);
        ForSharedSet.removeAll(OmpPrivSet);

        if (for_map.keySet().contains("shared")) {
            for_map.remove("shared");
        }
        for_map.put("shared", ForSharedSet);
        if (for_map.keySet().contains("private")) {
            for_map.remove("private");
        }
        for_map.put("private", OmpPrivSet);
        if (for_map.keySet().contains("threadprivate")) {
            for_map.remove("threadprivate");
        }
        for_map.put("threadprivate", OmpThreadPrivSet);

        displaySet("shared variables in a loop", ForSharedSet);
    }

    private HashSet<Symbol> getStaticVariables(Set<Symbol> iset) {
        HashSet<Symbol> ret = new HashSet<Symbol>();
        for (Symbol symbol : iset) {
            List<Specifier> type_specs = symbol.getTypeSpecifiers();
            for (Specifier spec : type_specs) {
                if (spec.toString().compareTo("static") == 0) {
                    ret.add(symbol);
                    break;
                }
            }
        }
        return ret;
    }

    /**
     * @param map  is a HashMap containing data attributes of an OpenMP parallel region.
     * @param stmt is either a CompoundStatement or a ForLoop
     */
    private HashSet<Symbol> findSharedInRegion(Map map, Statement stmt) {
        HashSet<String> tmp_set;
        debug_tab++;
        PrintTools.println("[findSharedInRegion] strt: " + stmt.getClass().getName(), 8);

        // shared variables explicitly defined by the OpenMP directive
        tmp_set = (HashSet<String>) map.get("shared");
        HashSet<Symbol> OmpSharedSet = convertString2Symbol(tmp_set, stmt);
        displaySet("OmpSharedSet in a region", OmpSharedSet);

        // private variables explicitly defined by the OpenMP directive
        tmp_set = (HashSet<String>) map.get("private");
        HashSet<Symbol> OmpPrivSet = convertString2Symbol(tmp_set, stmt);
        displaySet("OmpPrivSet in a region", OmpPrivSet);

        // In "C", the syntax is default(shared|none)
        // In a parallel or task construct, the data-sharing attributes of variables
        // are determined by the default clause, if present.
        // In a parallel construct, if no default clause if present, variables are shared
        boolean default_shared = true;
        if (map.keySet().contains("default")) {
            String default_value = (String) (map.get("default"));
            if (default_value.equals("none")) default_shared = false;
        }

        // add all accessed variable symbols in the procedure
        Set<Symbol> AccessedSet = getAccessedVariables(stmt);
        displaySet("AccessedSet in a region", AccessedSet);

        // -------------------------------------------------------------------
        // find the local variables declared locally within this parallel region
        // (both CompoundStatement and ForLoop have SymbolTable interface)
        // LocalPrivSet = local variables - static local - threadprivate
        // -------------------------------------------------------------------

        Set<Symbol> LocalPrivSet = new HashSet<Symbol>();

        // if stmt is CompoundStatement or ForLoop, it has SymbolTable interface
        // else if stmt is an ExpressionStatement that has a FunctionCall, do nothing
        if (stmt instanceof SymbolTable) {
            //LocalPrivSet.addAll( Tools.getVariableSymbols((SymbolTable)stmt) );
            LocalPrivSet.addAll(OMPDTools.getDeclaredSymbols(stmt)); //use this function to also retrieve symbols declared in inner scopes
            Set<Symbol> StaticLocalSet = getStaticVariables(LocalPrivSet);
            displaySet("static local variables in a region", StaticLocalSet);
            LocalPrivSet.removeAll(StaticLocalSet);
        }

        /*
           * "omp parallel" does not have threadprivate clause, but for other analysis, we
           * keep threadprivate set for each "omp parallel" region
           */
        tmp_set = (HashSet<String>) map.get("threadprivate");
        HashSet<Symbol> OmpThreadPrivSet = convertString2Symbol(tmp_set, stmt);
        displaySet("threadprivate variables in a region", OmpThreadPrivSet);
        LocalPrivSet.removeAll(OmpThreadPrivSet);

        // add loop index variables of parallel for loops to the LocalPrivSet
        HashSet<Symbol> LoopIndexVariables = new HashSet<Symbol>();
        if (stmt instanceof CompoundStatement) {
            LoopIndexVariables = getLoopIndexVarSet(stmt);
        } else if (stmt instanceof ForLoop) {
            Expression ivar_expr = LoopTools.getIndexVariable((ForLoop) stmt);
            Symbol ivar = SymbolTools.getSymbolOf(ivar_expr);
            LoopIndexVariables.add(ivar);
        }
        displaySet("parallel loop index variables in a region", LoopIndexVariables);
        LocalPrivSet.addAll(LoopIndexVariables);
        displaySet("LocalPrivSet = Local - Static - ThreadPrivate + ParallelLoopIndex", LocalPrivSet);

        //Omp private set contains local variables in current parallel region, stmt,
        //but does not include local variables in the called procedures.
        if (map.keySet().contains("private")) {
            map.remove("private");
        }
        OmpPrivSet.addAll(LocalPrivSet);
        map.put("private", OmpPrivSet);

        if (map.keySet().contains("threadprivate")) {
            map.remove("threadprivate");
        }
        map.put("threadprivate", OmpThreadPrivSet);

        // ------------------------------------------------------------------------------------------
        // Downward inter-procedural analysis
        // ipaSharedSet is a set of shared variables in the functions called within the current scope
        // ------------------------------------------------------------------------------------------
        Set<Symbol> IpaSharedSet = getIpaSharedSet(map, stmt);
        displaySet("IpaSharedSet", IpaSharedSet);

        // if default is shared
        //   SharedSet = AccessedSet + IpaSharedSet + OmpShared - OmpPriv - Local - ThreadPrivate
        // if default is none
        //   SharedSet = IpaSharedSet + OmpShared - OmpPriv - Local - ThreadPrivate
        HashSet<Symbol> SharedSet = new HashSet<Symbol>();
        if (default_shared) {
            SharedSet.addAll(AccessedSet);
        }
        SharedSet.addAll(IpaSharedSet);
        SharedSet.addAll(OmpSharedSet);
        SharedSet.removeAll(OmpPrivSet);
        SharedSet.removeAll(OmpThreadPrivSet);
//  SharedSet.removeAll(LocalPrivSet);

        displaySet("Final SharedSet in a region", SharedSet);

        PrintTools.println("[findSharedInRegion] done: " + stmt.getClass().getName(), 8);
        debug_tab--;
        return SharedSet;
    }

    /**
     * collect loop index variables for parallel for loops
     */
    private HashSet<Symbol> getLoopIndexVarSet(Statement stmt) {
        HashSet<Symbol> ret = new HashSet<Symbol>();
        DepthFirstIterator iter = new DepthFirstIterator(stmt);
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof OmpdAnnotation) {
                OmpdAnnotation ompdAnnotation = (OmpdAnnotation) obj;
                if (ompdAnnotation.containsKey("for")) {
                    ForLoop loop = (ForLoop) ompdAnnotation.getAnnotatable();
                    Expression ivar_expr = LoopTools.getIndexVariable(loop);
                    Symbol ivar = SymbolTools.getSymbolOf(ivar_expr);
                    if (ivar == null)
                        Tools.exit("[getLoopIndexVariables] Cannot find symbol:" + ivar.toString());
                    else
                        ret.add(ivar);
                }
            }
        }
        return ret;
    }

    /**
     * Interprocedural shared variable analysis driver
     */
    private HashSet<Symbol> getIpaSharedSet(Map map, Statement stmt) {
        HashSet<Symbol> SharedSet = new HashSet<Symbol>();
        DepthFirstIterator iter = new DepthFirstIterator(stmt);
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof FunctionCall) {
                FunctionCall call = (FunctionCall) obj;
                // called_procedure is null for system calls
                Procedure called_procedure = call.getProcedure();
                Set<Symbol> procSharedSet = null;
                if (called_procedure != null) {
                    //System.out.println("[getIpaSharedSet] proc="+call.toString());
                    // recursive call to findSharedInRegion routine
                    procSharedSet = findSharedInProcedure(map, called_procedure);
                    if (procSharedSet != null) {
                        displaySet("procSharedSet in " + called_procedure.getName(), procSharedSet);
                        SharedSet.addAll(procSharedSet);
                    }
                }
            }
        }
        return SharedSet;
    }

    /**
     * returns a set of all accessed symbols except Procedure symbols
     */
    private Set<Symbol> getAccessedVariables(Statement stmt) {
        Set<Symbol> set = SymbolTools.getAccessedSymbols(stmt);
        HashSet<Symbol> ret = new HashSet<Symbol>();
        for (Symbol symbol : set) {
            if ((symbol instanceof AccessSymbol) || (symbol instanceof NestedDeclarator) ||
                    (symbol instanceof VariableDeclarator)) {
                ret.add(symbol);
            }
        }
        return ret;
    }

    /**
     * Data-sharing Attribute Rules for Variables Referenced in a Region but not
     * in a Construct.
     * (1) Static variables declared in called routines in the region are shared.
     * (2) Variables with const-qualified type having no mutable member, and that
     *     are declared in called routines, are shared.
     * (3) File-scope or namespace-scope variables referenced in called routines in
     *     the region are shared unless they appear in a threadprivate directive.
     * (4) Variables with heap-allocated storage are shared.
     * (5) Static data members are shared unless they appear in a threadprivate directive.
     * (6) Formal arguments of called routines in the region that are passed by
     *     reference inherit the data-sharing attributes of the associated actual argument.
     * (7) Other variables declared in called routines in the region are private.
     */

    /**
     * recursive function call
     */
    private Set<Symbol> findSharedInProcedure(Map map, Procedure proc) {
        debug_tab++;
/*
		IDExpression expr = proc.getName();
		Symbol sss = expr.getSymbol();
		String str = sss.getSymbolName();	// NullPointerException here for conj_grad in CG
*/
        PrintTools.println("[findSharedInProcedure] strt: " + proc.getName().toString(), 6);
        CompoundStatement proc_body = proc.getBody();

        // find all local variables declared in the procedure body
        Set<Symbol> LocalPrivSet = SymbolTools.getVariableSymbols((SymbolTable) proc_body);
        displaySet("All local variables in a procedure", LocalPrivSet);

        Set<Symbol> SharedSet = new HashSet<Symbol>();
        // add all accessed variable symbols in the procedure
        Set<Symbol> accessedSymbols = getAccessedVariables(proc_body);
        displaySet("All accessed variables in a procedure", accessedSymbols);
        for (Symbol sm : accessedSymbols) {
            Traversable decl = sm.getDeclaration();
            if (decl == null) { //symbol is not passed as a parameter.
                SharedSet.add(sm); //it can be either a global or local variable.
            } else {
                if (SymbolTools.isScalar(sm)) { //Call-by-value parameter is a local variable
                    LocalPrivSet.add(sm);
                } else {
                    // Formal arguments of called routines that are passed by reference
                    // inherit the data-sharing attributes of the associated argument.
                    PrintTools.println("[OmpAnalsys.findSharedInProcedure()] Call-by-reference parameter " +
                            proc.getName().toString() + " should be handled by a caller", 2);
                }
            }
        }

        // find static variables in a procedure to check rule (1)
        Set<Symbol> StaticLocalSet = getStaticVariables(LocalPrivSet);
        displaySet("static local variables in a procedure", StaticLocalSet);

        // LocalPrivSet = LocalPrivSet - StaticLocalSet - ThreadPrivSet
        LocalPrivSet.removeAll(StaticLocalSet);

        HashSet<Symbol> OmpThreadPrivSet = (HashSet<Symbol>) map.get("threadprivate");
        displaySet("threadprivate variables in a procedure", OmpThreadPrivSet);
        LocalPrivSet.removeAll(OmpThreadPrivSet);

        // SharedSet = SharedSet - LocalSet - ThreadPrivSet
        SharedSet.removeAll(LocalPrivSet);
        SharedSet.removeAll(OmpThreadPrivSet);

        // index variables of omp for-loops are predetermined private variables,
        // which may or may not be listed in the data-sharing attribute clauses
        // In case if they are not listed, we add them to the private variables
        // SharedSet = SharedSet - LoopIndexVariables
        Set LoopIndexVariables = getLoopIndexVarSet(proc_body);
        SharedSet.removeAll(LoopIndexVariables);

        //Below is disabled so that omp private set does not contain private
        //variables in called procedures.
        //Update private set in the map
        //HashSet<Symbol> OmpPrivSet = (HashSet<Symbol>)map.get("private");
        //OmpPrivSet.addAll(LocalPrivSet);
        //OmpPrivSet.addAll(LoopIndexVariables);

        DepthFirstIterator iter = new DepthFirstIterator(proc_body);
        while (iter.hasNext()) {
            Object obj = iter.next();
            if (obj instanceof FunctionCall) {
                FunctionCall call = (FunctionCall) obj;

                // called_proc is null for system calls
                Procedure called_proc = call.getProcedure();

                if (called_proc != null) {
                    // recursive call to findSharedInProcedure routine
                    PrintTools.println("Performing IPA into the procedure: " + called_proc.getName(), 6);
                    Set<Symbol> procSharedSet = findSharedInProcedure(map, called_proc);
                    if (procSharedSet != null) {
                        displaySet("procSharedSet in " + called_proc.getName(), procSharedSet);
                        SharedSet.addAll(procSharedSet);
                    }
                }
            }
        }

        PrintTools.println("[findSharedInProcedure] done: " + proc.getName().toString(), 6);
        PrintTools.println("--------------------------------------", 6);

        debug_tab--;
        return SharedSet;
    }

    /**
     * convert a set of String into a set of Symbols
     *
     * @param stmt is either a CompoundStatement or ForLoop, where a matching symbol
     *             is searched for a given String. We assume that there should be only one matching
     *             symbol within a stmt
     */
    private HashSet<Symbol> convertString2Symbol(Set<String> iset, Statement stmt) {
        HashSet<Symbol> ret = new HashSet<Symbol>();
        if (iset == null) return ret;

        Set<Symbol> accessed_set = getAccessedVariables(stmt);
        for (Symbol sym : accessed_set) {
            String str = sym.getSymbolName();
            if (iset.contains(str)) {
                ret.add(sym);
            }
        }
        return ret;
    }

    private AnnotationStatement insertBarrier(Statement stmt, String type) {
        OmpdAnnotation ompdAnnotation = new OmpdAnnotation();
        ompdAnnotation.put("barrier", type);
        ompdAnnotation.put("source", stmt);
        AnnotationStatement annot_stmt = new AnnotationStatement(ompdAnnotation);
        return annot_stmt;
    }

    /**
     * Implicit barrier
     * - at the end of the parallel construct
     * - at the end of the worksharing construct (check an existence of nowait clause)
     * - at the end of the sections construct (check an existence of nowait clause)
     * - at the end of the single construct (check an existence of nowait clause)
     */

    public void mark_intervals() {
        PrintTools.println("[mark_intervals] strt", 5);

        List<OmpdAnnotation> ompdAnnotationList = OMPDTools.collectPragmas(program, OmpdAnnotation.class);

        for (OmpdAnnotation ompdAnnotation : ompdAnnotationList) {
            Object obj = ompdAnnotation.getAnnotatable();
            if (!(obj instanceof Statement))
                continue;

            Statement ownerStatement;
            CompoundStatement parentStatement;

            ownerStatement = (Statement)obj;
            parentStatement = (CompoundStatement) ownerStatement.getParent();
            if (ompdAnnotation.containsKey("parallel") && ompdAnnotation.containsKey("for")) {
                /*
                * No need to make a barrier before a parallel region, because
                *   1. DEF's in serial region are already shared by all processes.
                *   2. If there is a parallel region before this parallel region,
                *      the previous parallel region already created a barrier.
                * parent_stmt.addStatementBefore(attached_stmt, insertBarrier(attached_stmt, "S2P"));
                */
                if (ompdAnnotation.containsKey("nowait") == false)
                {
                    parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2S"));
                }
            } else if (ompdAnnotation.containsKey("parallel")) {
                parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2S"));

                PrintTools.println("[mark] parent_stmt", 10);
                PrintTools.println(parentStatement.toString(), 10);
            } else if (ompdAnnotation.containsKey("for") || ompdAnnotation.containsKey("sections") ||
                    ompdAnnotation.containsKey("single")) {
                if (ompdAnnotation.containsKey("nowait") == false)
                {
                    parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2P"));
                }
            } else if (ompdAnnotation.containsKey("barrier")) {
                /* store source statement that will be used in PCFG */
                ompdAnnotation.put("source", ownerStatement);
            }
        }

        PrintTools.println("[mark_intervals] done", 5);
    }

    /**
     * This method is for debugging purpose; it shows the statement that
     * has an OpenMP pragma.
     */
    public void display() {
        if (debug_level < 8) return;

        List<OmpdAnnotation> ompdAnnotationList = OMPDTools.collectPragmas(program, OmpdAnnotation.class);

        for (OmpdAnnotation ompdAnnotation : ompdAnnotationList) {
            System.out.println("has the following OpenMP pragmas");
            for (String ikey : ompdAnnotation.keySet()) {    // (key, set) pairs
                if (ikey.compareTo("private") == 0 ||
                        ikey.compareTo("firstprivate") == 0 ||
                        ikey.compareTo("lastprivate") == 0 ||
                        ikey.compareTo("shared") == 0 ||
                        ikey.compareTo("copyprivate") == 0 ||
                        ikey.compareTo("copyin") == 0 ||
                        ikey.compareTo("threadprivate") == 0 ||
                        ikey.compareTo("flush") == 0) {
                    System.out.print("[" + ikey + "] (");
                    displaySet((Set<String>) (ompdAnnotation.get(ikey)));
                    System.out.println(")");
                } else if (ikey.compareTo("critical") == 0 ||
                        ikey.compareTo("if") == 0 ||
                        ikey.compareTo("num_threads") == 0 ||
                        ikey.compareTo("schedule") == 0 ||
                        ikey.compareTo("collapse") == 0 ||
                        ikey.compareTo("default") == 0) {    // (key, string) pairs
                    System.out.print("[" + ikey + "] (");
                    System.out.print(ompdAnnotation.get(ikey));
                    System.out.println(")");
                } else if (ikey.compareTo("reduction") == 0) {    // ("reduction", reduction_map) pair
                    HashMap reduction_map = (HashMap) (ompdAnnotation.get(ikey));
                    System.out.print("[" + ikey + "] ");
                    for (String op : (Set<String>) (reduction_map.keySet())) {
                        System.out.print("(" + op + ": ");
                        displaySet((Set<String>) (reduction_map.get(op)));
                        System.out.print(")");
                    }
                    System.out.println();
                } else {    // (key, "true") pairs
                    System.out.println("[" + ikey + "]");
                }
            }
        }
    }

    public void displayList(LinkedList<String> list) {
        int cnt = 0;
        if (debug_level > 1) {
            for (int i = 0; i < debug_tab; i++) System.out.print("  ");
            for (String ilist : list) {
                if ((cnt++) != 0) System.out.print(", ");
                System.out.print(ilist);
            }
        }
    }

    public void displaySet(Set iset) {
        int cnt = 0;
        if (iset == null) return;
        if (debug_level > 1) {
            for (int i = 0; i < debug_tab; i++) System.out.print("  ");
            for (Object obj : iset) {
                if ((cnt++) != 0) System.out.print(", ");
                if (obj instanceof String)
                    System.out.print((String) obj);
                else if (obj instanceof Symbol)
                    System.out.print(((Symbol) obj).getSymbolName());
            }
        }
    }

    public void displaySet(String name, Set iset) {
        int cnt = 0;
        if (iset == null) return;
        if (debug_level > 1) {
            for (int i = 0; i < debug_tab; i++) System.out.print("  ");
            System.out.print(name + ": ");
            for (Object obj : iset) {
                if ((cnt++) != 0) System.out.print(", ");
                if (obj instanceof String)
                    System.out.print((String) obj);
                else if (obj instanceof Symbol)
                    System.out.print(((Symbol) obj).getSymbolName());
            }
            System.out.println("\n");
        }
    }

    public HashSet convert2SetOfStrings(Set iset) {
        HashSet oset = new HashSet();
        if (iset == null) return null;
        for (Object obj : iset) {
            if (obj instanceof Symbol) oset.add(((Symbol) obj).getSymbolName());
            else if (obj instanceof Expression) {
                if (obj instanceof ArrayAccess)
                    oset.add((((ArrayAccess) obj).getArrayName()).toString());
                else
                    oset.add(((Expression) obj).toString());
            } else
                System.out.println("Error");
        }
        return oset;
    }

    static private String[] omp_pragma_w_attach = {
            "parallel", "for", "sections", "section", "single", "task",
            "master", "critical", "atomic", "ordered"
    };
/*	static private String[] omp_pragma_wo_attach = {
		"barrier", "taskwait", "flush", "threadprivate"
	};*/

    /**
     * Useful for passing to setPrintMethod or setClassPrintMethod.
     * Specially this is useful to print omp threadprivate pragma, which
     * can exist as a Declaration, not wrapped by AnnotationStatement,
     * in a TranslationUnit.
     *
     * @param note   : OmpAnnotation to be printed
     * @param stream : OutputStream
     */
    public static void printAsOmpPragma(OmpAnnotation note, OutputStream stream) {
        PrintStream p = new PrintStream(stream);

        p.print(note.toString());
    }

//------------------------------------------------------------------------------------------
// Below code is commented out because no one uses it, but is left for historical records.
//------------------------------------------------------------------------------------------
//
//    /**
//     * Update information of OmpAnnotations contained in the region.
//     * If input region is a cloned one, both cloned OmpAnnotation and original OmpAnnotation
//     * will refer to the same map, and thus this method recreates OmpAnnotations
//     * for each cloned OmpAnnotation to have its own map.
//     * For each OmpAnnotation whose Pragma name is pragma
//     * - shared, private, reduction, and threadprivate data sets are updated.
//     * - Link information of the attached statement is updated.
//     *
//     * @param region code region where OmpAnnotations will be updated.
//     * @param pragma Pragma name of OmpAnnotations that will be updated (ex: "cetus" or "omp").
//     */
//    static public void updateOmpAnnotationsInRegion(Traversable region, String pragma) {
//        Annotation old_annot = null;
//        OmpAnnotation omp_annot = null;
//        AnnotationStatement annot_stmt = null;
//        AnnotationStatement ref_stmt = null;
//        boolean attach_to_the_next_stmt = false;
//        // omp_map: HashMap with an OpenMP construct as a key and a list of OpenMP HashMaps
//        HashMap old_map = null;
//        HashMap omp_map = null;
//        HashSet<Symbol> old_set = null;
//        HashSet<Symbol> new_set = null;
//
//        List pragma_w_attach = Arrays.asList(omp_pragma_w_attach);
//        //List pragma_wo_attach = Arrays.asList(omp_pragma_wo_attach);
//
//        /* iterate over everything, with particular attention to annotations */
//        DepthFirstIterator iter = new DepthFirstIterator(region);
//
//        while (iter.hasNext()) {
//            Object obj = iter.next();
//
//            /*
//             * Recreate AnnotationStatement so that included OmpAnnotation can have
//             * its own hash map.
//             * AnnotationStatement has Annotation as a private member.
//             */
//            if (obj instanceof AnnotationStatement) {
//                old_annot = ((AnnotationStatement) obj).getAnnotation();
//                /////////////////////////////////////////////////////////////////
//                // If old_annot is not an instance of OmpAnnotation, it may be //
//                // used to hold comments, but neither OpenMP nor Cetus pragma. //
//                /////////////////////////////////////////////////////////////////
//                if (!(old_annot instanceof OmpAnnotation)) {
//                    continue;
//                }
//                /////////////////////////////////////////////////////////////
//                // [CAUTION] if a barrier contains some useful data, below //
//                // may be removed.                                         //
//                /////////////////////////////////////////////////////////////
//                if (Tools.containsAnnotation(old_annot, "cetus", "barrier")) {
//                    continue;
//                }
//                old_map = (HashMap) old_annot.getMap();
//                omp_annot = new OmpAnnotation(old_annot.getText());
//                annot_stmt = new AnnotationStatement(omp_annot);
//                omp_map = (HashMap) (omp_annot.getMap());
//                omp_map.putAll(old_map);
//                annot_stmt.swapWith((AnnotationStatement) obj);
//                if (omp_annot.getText().compareTo(pragma) == 0) {
//                    if (Collections.disjoint(pragma_w_attach, omp_map.keySet())) {
//                        ////////////////////////////////////////////////////////////////////////
//                        // A barrier annotation can be inserted between an omp annotation and //
//                        // a statement to be attached. Thus, ignore barrier annotations.      //
//                        ////////////////////////////////////////////////////////////////////////
//                        if (!Tools.containsAnnotation(omp_annot, "cetus", "barrier")) {
//                            // Attach itself as an attachedStatement.
//                            // This is for compatibility with OmpAnalysis.start().
//                            annot_stmt.attachStatement(annot_stmt);
//                            attach_to_the_next_stmt = false;
//                        }
//                    } else {
//                        ref_stmt = annot_stmt;
//                        attach_to_the_next_stmt = true;
//                    }
//                }
//            } else if (attach_to_the_next_stmt && (obj instanceof Statement)) {
//                if ((obj instanceof CompoundStatement) || (obj instanceof ForLoop) ||
//                        (obj instanceof ExpressionStatement)) {
//                    if (ref_stmt != null) {
//                        ref_stmt.attachStatement((Statement) obj);
//                        omp_annot = (OmpAnnotation) ref_stmt.getAnnotation();
//                        omp_map = (HashMap) (omp_annot.getMap());
//                        // Update omp shared, private, reduction, and threadprivate data sets.
//                        if (omp_map.keySet().contains("shared")) {
//                            old_set = (HashSet<Symbol>) omp_map.remove("shared");
//                            new_set = new HashSet<Symbol>();
//                            updateSymbols((Traversable) obj, old_set, new_set, true);
//                            omp_map.put("shared", new_set);
//                        }
//                        if (omp_map.keySet().contains("private")) {
//                            old_set = (HashSet<Symbol>) omp_map.remove("private");
//                            new_set = new HashSet<Symbol>();
//                            updateSymbols((Traversable) obj, old_set, new_set, false);
//                            omp_map.put("private", new_set);
//                        }
//                        if (omp_map.keySet().contains("threadprivate")) {
//                            old_set = (HashSet<Symbol>) omp_map.remove("threadprivate");
//                            new_set = new HashSet<Symbol>();
//                            updateSymbols((Traversable) obj, old_set, new_set, false);
//                            omp_map.put("threadprivate", new_set);
//                        }
//                        if (omp_map.keySet().contains("reduction")) {
//                            updateReductionClause((Traversable) obj, omp_map);
//                        }
//                        ref_stmt = null;
//                    }
//                    attach_to_the_next_stmt = false;
//                }
//            }
//        }
//    }
//
//    /**
//     * Create a HashMap which contains updated shared, reduction, private, and threadprivate data sets
//     * for the function called in a Omp parallel region. Depending on the sharing attributes of
//     * the actual arguments of the called function, corresponding formal parameters are
//     * assigned to one of HashSets (shared, reduction, private, and threadprivate sets) in the HashMap.
//     * In addition, shared data that are accessed in the called function, but not passed
//     * as parameters are added into the new shared set, and all local variables are added to
//     * the new private set.
//     *
//     * @param par_map HashMap of an enclosing parallel region.
//     * @param argList List of actual arguments passed into the function proc.
//     * @param proc    Procedure that is called in a parallel region.
//     * @return New HashMap that contains updated shared, private, and threadprivate data sets.
//     */
//    static private HashMap updateOmpMapForCalledFunc(HashMap par_map, List<Expression> argList, Procedure proc) {
//        HashSet<Symbol> old_set = null;
//        HashSet<Symbol> new_set = null;
//        HashSet<Symbol> argSyms = new HashSet<Symbol>();
//        HashMap new_map = new HashMap();
//        // Copy all hash mapping except for shared, private, and threadprivate data sets
//        new_map.putAll(par_map);
//        new_map.remove("shared");
//        new_map.remove("reduction");
//        new_map.remove("private");
//        new_map.remove("threadprivate");
//
//        Set<Symbol> accessedSymbols = Tools.getAccessedSymbols(proc.getBody());
//
//        List paramList = proc.getParameters();
//        int list_size = paramList.size();
//        for (int i = 0; i < list_size; i++) {
//            Symbol sm = Tools.getSymbolOf(argList.get(i));
//            argSyms.add(sm);
//        }
//        if (par_map.keySet().contains("shared")) {
//            old_set = (HashSet<Symbol>) par_map.get("shared");
//            new_set = new HashSet<Symbol>();
//            // If actual argument is shared, put corresponding parameter into the new shared set.
//            for (int i = 0; i < list_size; i++) {
//                Symbol sm = Tools.getSymbolOf(argList.get(i));
//                if (old_set.contains(sm)) {
//                    Object obj = paramList.get(i);
//                    if (obj instanceof VariableDeclaration) {
//                        VariableDeclarator vdecl =
//                                (VariableDeclarator) ((VariableDeclaration) obj).getDeclarator(0);
//                        new_set.add(vdecl);
//                    }
//                }
//            }
//            // Put other shared variables in the old_set, which are accessed
//            // in the called function, into the new set.
//            for (Symbol ssm : old_set) {
//                if (!argSyms.contains(ssm)) {
//                    if (accessedSymbols.contains(ssm)) {
//                        new_set.add(ssm);
//                    }
//                }
//            }
//            new_map.put("shared", new_set);
//        }
//
//        if (par_map.keySet().contains("reduction")) {
//            HashMap reduction_map = (HashMap) par_map.get("reduction");
//            HashMap newreduction_map = new HashMap(4);
//            HashSet<Symbol> allItemsSet = new HashSet<Symbol>();
//            for (String ikey : (Set<String>) (reduction_map.keySet())) {
//                HashSet<Symbol> o_set = (HashSet<Symbol>) reduction_map.get(ikey);
//                HashSet<Symbol> n_set = new HashSet<Symbol>();
//                // If actual argument is a reduction variable, put corresponding
//                // parameter into the new reduction set.
//                for (int i = 0; i < list_size; i++) {
//                    Symbol sm = Tools.getSymbolOf(argList.get(i));
//                    if (o_set.contains(sm)) {
//                        Object obj = paramList.get(i);
//                        if (obj instanceof VariableDeclaration) {
//                            VariableDeclarator vdecl =
//                                    (VariableDeclarator) ((VariableDeclaration) obj).getDeclarator(0);
//                            n_set.add(vdecl);
//                        }
//                    }
//                }
//                // Put other reduction variables in the o_set, which are accessed
//                // in the called function, into the n_set.
//                for (Symbol ssm : o_set) {
//                    if (!argSyms.contains(ssm)) {
//                        if (accessedSymbols.contains(ssm)) {
//                            n_set.add(ssm);
//                        }
//                    }
//                }
//                newreduction_map.put(ikey, n_set);
//            }
//            new_map.put("reduction", newreduction_map);
//        }
//        /*
//           * FIXME: What if a private variable is passed as a reference?
//           */
//        if (par_map.keySet().contains("private")) {
//            old_set = (HashSet<Symbol>) par_map.get("private");
//            new_set = new HashSet<Symbol>();
//            // If actual argument is private, put corresponding parameter into the new private set.
//            for (int i = 0; i < list_size; i++) {
//                Symbol sm = Tools.getSymbolOf(argList.get(i));
//                if (old_set.contains(sm)) {
//                    Object obj = paramList.get(i);
//                    if (obj instanceof VariableDeclaration) {
//                        VariableDeclarator vdecl = (VariableDeclarator) ((VariableDeclaration) obj).getDeclarator(0);
//                        if (Tools.isScalar(vdecl)) {
//                            new_set.add(vdecl);
//                        } else {
//                            Tools.println("[Caution] private variable is passed as a reference in procedure, " +
//                                    proc.getName().toString() + "; splitting parallel region may result in "
//                                    + "incorrect output codes.", 0);
//                            new_set.add(vdecl);
//                        }
//                    }
//                }
//            }
//            // Put other private variables that are declared within this function call.
//            Set<Symbol> localSymbols = new HashSet<Symbol>();
//            DepthFirstIterator iter = new DepthFirstIterator(proc.getBody());
//            while (iter.hasNext()) {
//                Object obj = iter.next();
//                if (obj instanceof SymbolTable) {
//                    localSymbols.addAll(Tools.getVariableSymbols((SymbolTable) obj));
//                }
//            }
///*			for( Symbol ssm : localSymbols ) {
//				if( !argSyms.contains(ssm) ) {
//						new_set.add(ssm);
//				}
//			}*/
//            new_set.addAll(localSymbols);
//            new_map.put("private", new_set);
//        }
//        if (par_map.keySet().contains("threadprivate")) {
//            old_set = (HashSet<Symbol>) par_map.get("threadprivate");
//            new_set = new HashSet<Symbol>();
//            for (int i = 0; i < list_size; i++) {
//                Symbol sm = Tools.getSymbolOf(argList.get(i));
//                if (old_set.contains(sm)) {
//                    Object obj = paramList.get(i);
//                    if (obj instanceof VariableDeclaration) {
//                        VariableDeclarator vdecl = (VariableDeclarator) ((VariableDeclaration) obj).getDeclarator(0);
//                        new_set.add(vdecl);
//                    }
//                }
//            }
//            new_map.put("threadprivate", new_set);
//        }
//
//        // Update annotations of omp-for loops enclosed by the called procedure, proc.
//        List<AnnotationStatement> ompfor_annotList = (List<AnnotationStatement>)
//                Tools.getAnnotationStatementList(proc.getBody(), "cetus", "for");
//        for (AnnotationStatement annot_stmt : ompfor_annotList) {
//            Annotation annot = annot_stmt.getAnnotation();
//            HashMap map = (HashMap) (annot.getMap());
//            Statement attached_stmt = annot_stmt.getStatement();
//            accessedSymbols = Tools.getAccessedSymbols(attached_stmt);
//            if (map.keySet().contains("shared")) {
//                HashSet<Symbol> o_set = (HashSet<Symbol>) map.remove("shared");
//                HashSet<Symbol> n_set = new HashSet<Symbol>();
//                new_set = (HashSet<Symbol>) new_map.get("shared");
//                for (Symbol sm : new_set) {
//                    if (accessedSymbols.contains(sm)) {
//                        n_set.add(sm);
//                    }
//                }
//                for (Symbol sm : o_set) {
//                    if (!n_set.contains(sm)) {
//                        n_set.add(sm);
//                    }
//                }
//                map.put("shared", n_set);
//            }
//        }
//        return new_map;
//    }
//
//    /**
//     * For each symbol in the old_set,
//     * If it is accessed in the region t,
//     * - find a symbol with the same name in the SymbolTable,
//     * and put the new symbol into the new_set.
//     * - If no symbol is found in the table, put the old symbol into the new_set
//     *
//     * @param t        region, from which symbol search starts.
//     * @param old_set  Old Symbol data set from OmpAnnotation.
//     * @param new_set  New Symbol data set to be replaced for the old_set.
//     * @param isShared True if this update is for the shared data set.
//     */
//    static private void updateSymbols(Traversable t, HashSet<Symbol> old_set, HashSet<Symbol> new_set,
//                                      boolean isShared) {
//        VariableDeclaration sm_decl = null;
//        VariableDeclarator v_declarator = null;
//        Traversable tt = t;
//        while (!(tt instanceof SymbolTable)) {
//            tt = tt.getParent();
//        }
//        Set<Symbol> accessedSymbols = Tools.getAccessedSymbols(t);
//        if (isShared) {
//            List<FunctionCall> calledFuncs = Tools.getFunctionCalls(t);
//            for (FunctionCall call : calledFuncs) {
//                Procedure called_procedure = call.getProcedure();
//                if (called_procedure != null) {
//                    CompoundStatement body = called_procedure.getBody();
//                    Set<Symbol> procAccessedSymbols = Tools.getAccessedSymbols(body);
//                    Set<Symbol> procLocalSymbols = Tools.getVariableSymbols(body);
//                    Set<Symbol> procSharedSymbols = new HashSet<Symbol>();
//                    procSharedSymbols.addAll(procAccessedSymbols);
//                    procSharedSymbols.removeAll(procLocalSymbols);
//                    accessedSymbols.addAll(procSharedSymbols);
//                }
//            }
//        }
//        for (Symbol sm : old_set) {
//            // Remove symbols that are not accessed in the region t.
//            // Because symbols in the region may not have been updated,
//            // use string comparison.
//            boolean accessed = false;
//            for (Symbol accSym : accessedSymbols) {
//                if (sm.getSymbolName().compareTo(accSym.getSymbolName()) == 0) {
//                    accessed = true;
//                    break;
//                }
//            }
//            if (accessed) {
//                sm_decl = (VariableDeclaration) Tools.findSymbol((SymbolTable) tt,
//                        ((VariableDeclarator) sm).getSymbol());
//                if (sm_decl == null) {
//                    new_set.add(sm);
//                } else {
//                    boolean found_sm = false;
//                    for (int i = 0; i < sm_decl.getNumDeclarators(); i++) {
//                        v_declarator = ((VariableDeclarator) sm_decl.getDeclarator(i));
//                        if (v_declarator.getSymbolName().compareTo(sm.getSymbolName()) == 0) {
//                            new_set.add(v_declarator);
//                            found_sm = true;
//                            break;
//                        }
//                    }
//                    if (!found_sm) {
//                        new_set.add(sm);
//                    }
//                }
//            }
//        }
//    }
//
//    /**
//     * Split omp parallel regions in the program at every explicit/implicit barrier.
//     * This split may break the correctness of the program if private data written in
//     * one split parallel subregion should be read in the other split parallel subregion.
//     * [CAUTION] New parallel regions split by this method will contain accurate
//     * annotations for each parallel region, but omp-for annotations in parallel regions
//     * may not have accurate information.
//     */
//    public void splitParallelRegions() {
//        Tools.println("[splitParallelRegions] strt", 5);
//
//        HashSet<String> visitedProcs = new HashSet<String>();
//        List<AnnotationStatement> pRegionAnnotStmts = new LinkedList<AnnotationStatement>();
//        DepthFirstIterator iter = new DepthFirstIterator(program);
//
//        while (iter.hasNext()) {
//            Object obj = iter.next();
//
//            if (obj instanceof AnnotationStatement) {
//                AnnotationStatement annot_stmt = (AnnotationStatement) obj;
//                Statement attached_stmt = (Statement) annot_stmt.getStatement();
//
//                // CAUTION: not all annotations are instance of OmpAnnnotation.
//                // OmpAnnotation annot = (OmpAnnotation)annot_stmt.getAnnotation();
//                Annotation annot = annot_stmt.getAnnotation();
//
//                if (Tools.containsAnnotations(annot, "cetus", "parallel", "for")) {
//                    if (attached_stmt instanceof ForLoop) {
//                        ForLoop floop = (ForLoop) attached_stmt;
//                        Statement body = floop.getBody();
//                        List annot_list = Tools.getAnnotationStatementList(body, "cetus", "barrier");
//                        if (annot_list.size() != 0) {
//                            Tools.exit("Error in splitParallelRegions(): omp-for loop can not be split!");
//                        }
//                    } else {
//                        Tools.println("OmpAnnotation (" + annot.toString() + ") has wrong atatached statement",
//                                0);
//                    }
//                } else if (Tools.containsAnnotations(annot, "cetus", "parallel", "sections")) {
//                    if (attached_stmt instanceof CompoundStatement) {
//                        List annot_list = Tools.getAnnotationStatementList(attached_stmt, "cetus", "barrier");
//                        if (annot_list.size() != 0) {
//                            Tools.exit("Error in splitParallelRegions(): omp parallel sections can not be split!");
//                        }
//                    } else {
//                        Tools.println("OmpAnnotation (" + annot.toString() + ") has wrong atatached statement",
//                                0);
//                    }
//                } else if (Tools.containsAnnotation(annot, "cetus", "parallel")) {
//                    if (attached_stmt instanceof CompoundStatement) {
//                        if (ipaContainsBarrierInRegion(attached_stmt)) { //found a parallel region that may be split.
//                            pRegionAnnotStmts.add(annot_stmt);
//                        }
//                    } else {
//                        Tools.println("OmpAnnotation (" + annot.toString() +
//                                ") has wrong atatached statement", 0);
//                    }
//                }
//            }
//        }
//        if (pRegionAnnotStmts.size() == 0) {
//            Tools.println("[splitParallelRegions] No split operation is conducted.", 2);
//        } else {
//            for (AnnotationStatement annot_stmt : pRegionAnnotStmts) {
//                Statement attached_stmt = annot_stmt.getStatement();
//                List<AnnotationStatement> barrier_list = (List<AnnotationStatement>)
//                        Tools.getAnnotationStatementList(attached_stmt, "cetus", "barrier");
//                int num_barriers = barrier_list.size();
//                HashMap old_map = (HashMap) annot_stmt.getAnnotation().getMap();
//                createSubRegions(barrier_list, old_map);
//                // Split parallel regions in called functions
//                List<FunctionCall> calledFuncs = Tools.getFunctionCalls(attached_stmt);
//                for (FunctionCall call : calledFuncs) {
//                    Procedure called_procedure = call.getProcedure();
//                    /*
//                          * If called function is a system call, parse may not be able to find corresponding
//                          * function body, and in this case, call.getProcedure() will return null.
//                          */
//                    if ((called_procedure == null) ||
//                            visitedProcs.contains(called_procedure.getSymbolName())) {
//                        continue;
//                    } else {
//                        visitedProcs.add(called_procedure.getSymbolName());
//                        CompoundStatement body = called_procedure.getBody();
//                        barrier_list = (List<AnnotationStatement>) Tools.getAnnotationStatementList(
//                                body, "cetus", "barrier");
//                        HashMap new_map = updateOmpMapForCalledFunc(old_map,
//                                (List<Expression>) call.getArguments(), called_procedure);
//                        createSubRegions(barrier_list, new_map);
//                        /////////////////////////////////////////////////////////////////////////////////
//                        // FIXME: If called_procecure does not have any barrier, the above call does   //
//                        // not update Omp annotations using the new_map data, and thus Omp annotations //
//                        // in the procedure still contains old hashmap data. Therefore, the next       //
//                        // method, updateOmpAnnotationsInRegion(), can not update annotation accurately//
//                        // (more specifically, the next call can not handle cases where arguments of   //
//                        // the called procedure are shared variables.                                  //
//                        // ==> In a procedure called in a parallel region, omp-for annotations may not //
//                        //     have accurate information, missing shared data passed as parameters.    //
//                        //     ==> updateOmpMapForCalledFunc() updates omp-for in the called function. //
//                        /////////////////////////////////////////////////////////////////////////////////
//                        //Update OmpAnnotations
//                        updateOmpAnnotationsInRegion(called_procedure, "cetus");
//                    }
//                }
//
//                /*
//                     * If the parallel region contains barriers only in the functions called within this
//                     * region, createSubRegions() will not do any thing for the main parallel region.
//                     * Thus, the below section splits the main parallel region at every function call
//                     * containing barriers.
//                     */
//                if (num_barriers == 0) {
//                    int barIndex = 0;
//                    int pBarIndex = 0;
//                    int list_size = 0;
//                    CompoundStatement parent = (CompoundStatement) attached_stmt;
//                    List<Traversable> children = parent.getChildren();
//                    LinkedList<Traversable> temp_list = new LinkedList<Traversable>();
//                    barIndex = children.size() - 1;
//
//                    Traversable lastchild = children.get(barIndex);
//                    if (!ipaContainsBarrierInRegion(lastchild)) {
//                        //Insert a barrier at the end of this compound statement.
//                        parent.addStatement(insertBarrier(null, "true"));
//                        barIndex = barIndex + 1; //point to the last, newly-inserted barrier.
//                    }
//                    while (barIndex > 0) {
//                        pBarIndex = 0;
//                        Statement cur_barrier = (Statement) children.get(barIndex);
//                        for (int i = barIndex - 1; i >= 0; i--) {
//                            Traversable child = children.remove(i);
//                            if (ipaContainsBarrierInRegion(child)) {
//                                children.add(i, child);
//                                if (!(child instanceof AnnotationStatement)) {
//                                    pBarIndex = i;
//                                }
//                                break;
//                            } else {
//                                temp_list.add(child);
//                            }
//                        }
//                        list_size = temp_list.size();
//                        if (list_size > 0) {
//                            CompoundStatement pRegion = new CompoundStatement();
//                            for (int i = 0; i < list_size; i++) {
//                                pRegion.addStatement((Statement) temp_list.removeLast());
//                            }
//                            OmpAnnotation omp_annot = new OmpAnnotation("cetus");
//                            HashMap omp_map = (HashMap) omp_annot.getMap();
//                            omp_map.putAll(old_map);
//                            AnnotationStatement cloned_astmt = new AnnotationStatement(omp_annot);
//                            cloned_astmt.attachStatement(pRegion);
//                            parent.addStatementBefore(cur_barrier, cloned_astmt);
//                            //parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                            parent.addStatementBefore(cur_barrier, pRegion);
//                            if (cur_barrier instanceof AnnotationStatement) {
//                                ((AnnotationStatement) cur_barrier).attachStatement(pRegion);
//                            } else {
//                                parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                            }
//                        }
//                        barIndex = pBarIndex;
//                    }
//
//                }
//                //Update OmpAnnotations
//                updateOmpAnnotationsInRegion(attached_stmt, "cetus");
//
//                // When splitting occurs, old parallel region should be removed.
//                // To do so, old omp pragma is replaced with comment statement.
//                Annotation annot = annot_stmt.getAnnotation();
//                Annotation comment = new Annotation(annot.toString());
//                comment.setPrintMethod(Annotation.print_as_comment_method);
//                AnnotationStatement comment_stmt = new AnnotationStatement(comment);
//                annot_stmt.swapWith(comment_stmt);
//            }
//            Tools.println("[splitParallelRegions] done", 5);
//        }
//    }
//
//    /**
//     * Run interprocedural analysis to find whether the region contains a barrier or not.
//     *
//     * @param region : a region to be searched.
//     * @return : returns true if the region contains a barrier.
//     */
//    private boolean ipaContainsBarrierInRegion(Traversable region) {
//        boolean foundBarrier = false;
//        if (region instanceof AnnotationStatement) {
//            AnnotationStatement annot_stmt = (AnnotationStatement) region;
//            Annotation annot = annot_stmt.getAnnotation();
//            HashMap map = (HashMap) (annot.getMap());
//            if (annot.getText().compareTo("cetus") == 0 && map.keySet().contains("barrier")) {
//                return true;
//            } else {
//                return false;
//            }
//        }
//        DepthFirstIterator iter = new DepthFirstIterator(region);
//        while (iter.hasNext()) {
//            Object obj = iter.next();
//            if (obj instanceof AnnotationStatement) {
//                AnnotationStatement annot_stmt = (AnnotationStatement) obj;
//                Annotation annot = annot_stmt.getAnnotation();
//                HashMap map = (HashMap) (annot.getMap());
//                if (annot.getText().compareTo("cetus") == 0 && map.keySet().contains("barrier")) {
//                    foundBarrier = true;
//                    break;
//                }
//            } else if (obj instanceof FunctionCall) {
//                FunctionCall call = (FunctionCall) obj;
//                // called_procedure is null for system calls
//                Procedure called_procedure = call.getProcedure();
//                if (called_procedure != null) {
//                    foundBarrier = ipaContainsBarrierInRegion(called_procedure.getBody()); // recursive call
//                    if (foundBarrier) {
//                        break;
//                    }
//                }
//            }
//        }
//        return foundBarrier;
//    }
//
//    /**
//     * Split parallel region into two sub regions at every Barrier point.
//     * This method is called once for each main parallel region containing barriers,
//     * and if the parallel region contains function calls, this method is called
//     * again for each called function.
//     *
//     * @param barrier_list List of Barriers
//     * @param old_map      Omp HashMap of OmpAnnotation that refers to the enclosing parallel region
//     */
//    private void createSubRegions(List<AnnotationStatement> barrier_list, HashMap old_map) {
//        int barIndex = 0;
//        int pBarIndex = 0;
//        int list_size = 0;
//        for (AnnotationStatement barrier_stmt : barrier_list) {
//            Traversable t = barrier_stmt.getParent();
//            if (t instanceof CompoundStatement) {
//                CompoundStatement parent = (CompoundStatement) t;
//                List<Traversable> children = parent.getChildren();
//                LinkedList<Traversable> temp_list = new LinkedList<Traversable>();
//                barIndex = Tools.indexByReference(children, barrier_stmt);
//                pBarIndex = 0;
//                list_size = 0;
//                /*
//                     * Check statements between current barrier and previous barrier.
//                     * If there is no statement that contains a barrier inside, below splitting will
//                     * create one sub-egion, which is a parallel region.
//                     * Otherwise, the sub-region enclosed by both current barrier and previous barrier
//                     * should be split further at each statement containing a barrier internally.
//                     */
//                while (barIndex > 0) {
//                    pBarIndex = 0;
//                    Statement cur_barrier = (Statement) children.get(barIndex);
//                    for (int i = barIndex - 1; i >= 0; i--) {
//                        Traversable child = children.remove(i);
//                        if (ipaContainsBarrierInRegion(child)) {
//                            children.add(i, child);
//                            if (!(child instanceof AnnotationStatement)) {
//                                pBarIndex = i;
//                            }
//                            break;
//                        } else {
//                            temp_list.add(child);
//                        }
//                    }
//                    list_size = temp_list.size();
//                    if (list_size > 0) {
//                        CompoundStatement pRegion = new CompoundStatement();
//                        for (int i = 0; i < list_size; i++) {
//                            pRegion.addStatement((Statement) temp_list.removeLast());
//                        }
//                        OmpAnnotation omp_annot = new OmpAnnotation("cetus");
//                        HashMap omp_map = (HashMap) omp_annot.getMap();
//                        omp_map.putAll(old_map);
//                        AnnotationStatement cloned_astmt = new AnnotationStatement(omp_annot);
//                        cloned_astmt.attachStatement(pRegion);
//                        parent.addStatementBefore(cur_barrier, cloned_astmt);
//                        //parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                        parent.addStatementBefore(cur_barrier, pRegion);
//                        if (cur_barrier instanceof AnnotationStatement) {
//                            ((AnnotationStatement) cur_barrier).attachStatement(pRegion);
//                        } else {
//                            parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                        }
//                    }
//                    barIndex = pBarIndex;
//                }
//                /*
//                     * There can be a sub-region after the last barrier;
//                     * this last sub-region is handled here.
//                     */
//                barIndex = children.size() - 1;
//                temp_list.clear();
//                Traversable lastchild = children.get(barIndex);
//                boolean lastSubRHandled = false;
//                if (ipaContainsBarrierInRegion(lastchild)) {
//                    if (lastchild instanceof AnnotationStatement) {
//                        lastSubRHandled = true;
//                    }
//                } else { //Insert a barrier at the end of this compound statement.
//                    parent.addStatement(insertBarrier(null, "true"));
//                    barIndex = barIndex + 1; //point to the last, newly-inserted barrier.
//                }
//                if (!lastSubRHandled) {
//                    while (barIndex > 0) {
//                        pBarIndex = 0;
//                        Statement cur_barrier = (Statement) children.get(barIndex);
//                        for (int i = barIndex - 1; i >= 0; i--) {
//                            Traversable child = children.remove(i);
//                            if (ipaContainsBarrierInRegion(child)) {
//                                children.add(i, child);
//                                if (!(child instanceof AnnotationStatement)) {
//                                    pBarIndex = i;
//                                }
//                                break;
//                            } else {
//                                temp_list.add(child);
//                            }
//                        }
//                        list_size = temp_list.size();
//                        if (list_size > 0) {
//                            CompoundStatement pRegion = new CompoundStatement();
//                            for (int i = 0; i < list_size; i++) {
//                                pRegion.addStatement((Statement) temp_list.removeLast());
//                            }
//                            OmpAnnotation omp_annot = new OmpAnnotation("cetus");
//                            HashMap omp_map = (HashMap) omp_annot.getMap();
//                            omp_map.putAll(old_map);
//                            AnnotationStatement cloned_astmt = new AnnotationStatement(omp_annot);
//                            cloned_astmt.attachStatement(pRegion);
//                            parent.addStatementBefore(cur_barrier, cloned_astmt);
//                            //parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                            parent.addStatementBefore(cur_barrier, pRegion);
//                            if (cur_barrier instanceof AnnotationStatement) {
//                                ((AnnotationStatement) cur_barrier).attachStatement(pRegion);
//                            } else {
//                                parent.addStatementBefore(cur_barrier, insertBarrier(pRegion, "true"));
//                            }
//                        }
//                        barIndex = pBarIndex;
//                    }
//                }
//            }
//        }
//    }
//
//    /**
//     * Convert a set of Strings in each OpenMP reduction clause into a set of Symbols.
//     * - This method should be called right after OmpAnalysis.start() if your pass wants
//     * to handle OpenMP reduction clauses.
//     * - This method is not included in OmpAnalysis.start() before this method may modify
//     * shared set information if reduction clauses include shared variables; if a shared variable
//     * is used as a reduction variable, it should be removed from shared set (but if the
//     * reduction clause belongs to a work-sharing construct, the list item that appears in
//     * the reduction clause must be shared in the parallel region to which any of work-sharing
//     * regions arising from the work-sharing construct bind).
//     */
//    public void convertReductionClauses() {
//        List annot_stmts = Tools.getAnnotationStatementList(program, "cetus", "reduction");
//
//        for (AnnotationStatement annot_stmt : (List<AnnotationStatement>) annot_stmts) {
//            Statement stmt = annot_stmt.getStatement();
//            Annotation annot = annot_stmt.getAnnotation();
//            HashMap map = (HashMap) (annot.getMap());
//            //Check whether this annotation is derived from OpenMP annotation or not.
//            //Annotations generated by cetus.analysis.Reduction contain reduction clause only.
//            if (map.keySet().contains("parallel") || map.keySet().contains("for")
//                    || map.keySet().contains("sections")) {
//                HashMap reduction_map = (HashMap) map.remove("reduction");
//                HashMap newreduction_map = new HashMap(4);
//                for (String ikey : (Set<String>) (reduction_map.keySet())) {
//                    HashSet<String> tmp_set = (HashSet<String>) reduction_map.get(ikey);
//                    HashSet<Symbol> itemSet = convertString2Symbol(tmp_set, stmt);
//                    newreduction_map.put(ikey, itemSet);
//                    //newreduction_map.put(BinaryOperator.fromString(ikey), itemSet);
//                }
//                map.put("reduction", newreduction_map);
//                //Update reduction clause; remove unused reduction variables from
//                //the reduction itemlist, and remove shared variables from the shared
//                //set if they are included in the reduction itemlist.
//                updateReductionClause(stmt, map);
//
//            }
//        }
//    }
//
//    /*
//      * Restriction to the reduction clause (OpenMP API V3)
//      *     - A list item that appears in a reduction clause of a worksharing construct
//      *     must be shared in the parallel regions to which any of the worksharing regions
//      *     arising from the worksharing construct bind.
//      */
//
//    /**
//     * - For each symbol in the reduction itemlist,
//     * If it is accessed in the region t,
//     * - find a symbol with the same name in the SymbolTable,
//     * and put the new symbol into the reduction itemlist.
//     * - If no symbol is found in the table, put the old symbol into the itemlist.
//     * - If no symbol in the reduction itemlist is used in region, t,
//     * remove the reduction clause.
//     * FIXME: this method does not check whether any reduction variable is used
//     * in a function called within the region, t.
//     * - If any shared variable is included in the reduction itemlist,
//     * it should be removed from the shared set.
//     *
//     * @param t       region, from which symbol search starts.
//     * @param omp_map HashMap containing OpenMP clauses.
//     */
//    static private void updateReductionClause(Traversable t, HashMap omp_map) {
//        VariableDeclaration sm_decl = null;
//        VariableDeclarator v_declarator = null;
//        Traversable tt = t;
//        while (!(tt instanceof SymbolTable)) {
//            tt = tt.getParent();
//        }
//        Set<Symbol> accessedSymbols = Tools.getAccessedSymbols(t);
//        HashMap reduction_map = (HashMap) omp_map.remove("reduction");
//        HashMap newreduction_map = new HashMap(4);
//        HashSet<Symbol> allItemsSet = new HashSet<Symbol>();
//        for (String ikey : (Set<String>) (reduction_map.keySet())) {
//            HashSet<Symbol> old_set = (HashSet<Symbol>) reduction_map.get(ikey);
//            HashSet<Symbol> new_set = new HashSet<Symbol>();
//            for (Symbol sm : old_set) {
//                // Remove symbols that are not accessed in the region t.
//                // Because symbols in the region may not have been updated,
//                // use string comparison.
//                boolean accessed = false;
//                for (Symbol accSym : accessedSymbols) {
//                    if (sm.getSymbolName().compareTo(accSym.getSymbolName()) == 0) {
//                        accessed = true;
//                        break;
//                    }
//                }
//                if (accessed) {
//                    sm_decl = (VariableDeclaration) Tools.findSymbol((SymbolTable) tt,
//                            ((VariableDeclarator) sm).getSymbol());
//                    if (sm_decl == null) {
//                        new_set.add(sm);
//                    } else {
//                        boolean found_sm = false;
//                        for (int i = 0; i < sm_decl.getNumDeclarators(); i++) {
//                            v_declarator = ((VariableDeclarator) sm_decl.getDeclarator(i));
//                            if (v_declarator.getSymbolName().compareTo(sm.getSymbolName()) == 0) {
//                                new_set.add(v_declarator);
//                                found_sm = true;
//                                break;
//                            }
//                        }
//                        if (!found_sm) {
//                            new_set.add(sm);
//                        }
//                    }
//                }
//            }
//            if (new_set.size() > 0) {
//                //newreduction_map.put(BinaryOperator.fromString(ikey), itemSet);
//                newreduction_map.put(ikey, new_set);
//                allItemsSet.addAll(new_set);
//            }
//        }
//        if (allItemsSet.size() > 0) {
//            omp_map.put("reduction", newreduction_map);
//            //If any shared variable is included in the reduction itemlist,
//            //it should be removed from the shared set.
//            HashSet<Symbol> sharedSet = (HashSet<Symbol>) omp_map.get("shared");
//            HashSet<Symbol> deleteSet = new HashSet<Symbol>();
//            for (Symbol svar : sharedSet) {
//                for (Symbol redVar : allItemsSet) {
//                    if (svar.getSymbolName().compareTo(redVar.getSymbolName()) == 0) {
//                        deleteSet.add(svar);
//                        break;
//                    }
//                }
//            }
//            sharedSet.removeAll(deleteSet);
//        }
//    }
//
//    /**
//     * [Convert critical sections into reduction sections]
//     * For each critical section in a parallel region,
//     * if the critical section is a kind of reduction form, necessary reduction
//     * clause is added to the annotation of the enclosing parallel region, and
//     * the original critical construct is commented out.
//     * A critical section is considered as a reduction form if reduction variables recognized
//     * by Reduction.analyzeStatement2() are the only shared variables modified in the
//     * critical section.
//     * [CAUTION] Cetus compiler can recognize array reduction, but the array reduction
//     * is not supported by standard OpenMP compilers. Therefore, below conversion may
//     * not be handled correctly by other OpenMP compilers.
//     */
//    public void convertCritical2Reduction() {
//        List pRegion_stmts = Tools.getAnnotationStatementList(program, "cetus", "parallel");
//        Reduction redAnalysis = new Reduction(program);
//        for (AnnotationStatement pRegion_stmt : (List<AnnotationStatement>) pRegion_stmts) {
//            Statement pstmt = pRegion_stmt.getStatement();
//            Annotation pannot = pRegion_stmt.getAnnotation();
//            HashMap pRegionMap = (HashMap) (pannot.getMap());
//            HashSet<Symbol> shared_set = (HashSet<Symbol>) pRegionMap.get("shared");
//            HashMap pRedMap = (HashMap) pRegionMap.get("reduction");
//            List critical_stmts = Tools.getAnnotationStatementList(pstmt, "cetus", "critical");
//            for (AnnotationStatement critical_stmt : (List<AnnotationStatement>) critical_stmts) {
//                Statement cstmt = critical_stmt.getStatement();
//                Set<Symbol> definedSymbols = Tools.getDefSymbol(cstmt);
//                HashSet<Symbol> shared_subset = new HashSet<Symbol>();
//                shared_subset.addAll(shared_set);
//                Map<String, Set<Expression>> reduce_map = redAnalysis.analyzeStatement2(cstmt);
//                Map<String, Set<Symbol>> reduce_map2 = new HashMap<String, Set<Symbol>>();
//                if (!reduce_map.isEmpty()) {
//                    // Remove reduction variables from shared_subset.
//                    for (String ikey : (Set<String>) (reduce_map.keySet())) {
//                        Set<Expression> tmp_set = (Set<Expression>) reduce_map.get(ikey);
//                        HashSet<Symbol> redSet = new HashSet<Symbol>();
//                        for (Expression iexp : tmp_set) {
//                            //Symbol redSym = findsSymbol(shared_set, iexp.toString());
//                            Symbol redSym = Tools.getSymbolOf(iexp);
//                            if (redSym != null) {
//                                shared_subset.remove(redSym);
//                                redSet.add(redSym);
//                            }
//                        }
//                        reduce_map2.put(ikey, redSet);
//                    }
//                    //////////////////////////////////////////////////////////////////////
//                    // If shared_subset and definedSymbols are disjoint,                //
//                    // it means that reduction variables are the only shared variables  //
//                    // defined in the critical section.                                 //
//                    //////////////////////////////////////////////////////////////////////
//                    if (Collections.disjoint(shared_subset, definedSymbols)) {
//                        if (pRedMap == null) {
//                            pRedMap = new HashMap();
//                            pRegionMap.put("reduction", pRedMap);
//                        }
//                        for (String ikey : (Set<String>) (reduce_map2.keySet())) {
//                            Set<Symbol> tmp_set = (Set<Symbol>) reduce_map2.get(ikey);
//                            HashSet<Symbol> redSet = (HashSet<Symbol>) pRedMap.get(ikey);
//                            if (redSet == null) {
//                                redSet = new HashSet<Symbol>();
//                                pRedMap.put(ikey, redSet);
//                            }
//                            redSet.addAll(tmp_set);
//                        }
//                        Annotation annot = critical_stmt.getAnnotation();
//                        Annotation comment = new Annotation(annot.toString());
//                        comment.setPrintMethod(Annotation.print_as_comment_method);
//                        AnnotationStatement comment_stmt = new AnnotationStatement(comment);
//                        critical_stmt.swapWith(comment_stmt);
//                    }
//                }
//            }
//        }
//    }
//
//    /**
//     * Returns true if the symbol set contains a symbol whose name is the specified string.
//     *
//     * @param sset    Symbol set being searched
//     * @param symName symbol name being searched for
//     */
//    public static boolean containsSymbol(Set<Symbol> sset, String symName) {
//        if (sset == null)
//            return false;
//
//        for (Symbol sym : sset) {
//            if (sym.getSymbolName().equals(symName)) {
//                return true;
//            }
//        }
//
//        return false;
//    }
//
//    /**
//     * Searches the symbol set and returns the first symbol whose name is the specified string
//     *
//     * @param sset    Symbol set being searched
//     * @param symName symbol name being searched for
//     * @return the first symbol amaong the symbol set whose name is the same as the specified string
//     */
//    public static Symbol findsSymbol(Set<Symbol> sset, String symName) {
//        if (sset == null)
//            return null;
//
//        for (Symbol sym : sset) {
//            if (sym.getSymbolName().equals(symName)) {
//                return sym;
//            }
//        }
//
//        return null;
//    }
//
//
//    /**
//     * Clean up old OpenMP pragmas, which have the form of "#pragma omp ...".
//     * Depending on input parameter, commented, they will be commented out or
//     * removed.
//     *
//     * @param commented if true, old OpenMP pragmas are commented out.
//     *                  Otherwise, old OpenMP pragmas will be removed.
//     */
//    public void cleanOldOmpPragma(boolean commented) {
//        DepthFirstIterator iter = new DepthFirstIterator(program);
//        HashMap<Traversable, HashSet> removeMap =
//                new HashMap<Traversable, HashSet>();
//        HashSet<Traversable> removeSet = null;
//
//        while (iter.hasNext()) {
//            Object obj = iter.next();
//            //////////////////////////////////////////////////////////////////////////
//            // CAUTION: Below condition will only catch annotations that are not    //
//            // enclosed by AnnotationStatement; all OmpAnnotations exist            //
//            // as a private member of AnnotationStatements, and thus OmpAnnotations //
//            // will not be catched by this condition.                               //
//            //////////////////////////////////////////////////////////////////////////
//            if (obj instanceof Annotation) {
//                Annotation annot = (Annotation) obj;
//                String pragma = annot.getText();
//                if (pragma.startsWith("#pragma omp")) {
//                    if (commented) {
//                        ////////////////////////////////////////////////////////////////////////
//                        // FIXME: OmpAnnotation.toString() always print itselt as a pragma,   //
//                        // even though object print method is set to print_as_comment_method. //
//                        ////////////////////////////////////////////////////////////////////////
//                        annot.setPrintMethod(Annotation.print_as_comment_method);
//                    } else {
//                        Traversable cparent = annot.getParent();
//                        if (cparent instanceof Statement) {
//                            removeSet = removeMap.get(cparent.getParent());
//                            if (removeSet == null) {
//                                removeSet = new HashSet<Traversable>();
//                                removeMap.put(cparent.getParent(), removeSet);
//                            }
//                            removeSet.add(cparent);
//                        } else if (cparent instanceof TranslationUnit) {
//                            ////////////////////////////////////////////////////////////
//                            // Some pragma can exist as a Declaration, which does not //
//                            // have wrapping Statement, in a TranslationUnit.         //
//                            ////////////////////////////////////////////////////////////
//                            removeSet = removeMap.get(cparent);
//                            if (removeSet == null) {
//                                removeSet = new HashSet<Traversable>();
//                                removeMap.put(cparent, removeSet);
//                            }
//                            removeSet.add(annot);
//                        } else {
//                            Tools.exit("[cleanOldOmpPragma()] Unexpected Annotation is found => " + annot);
//                        }
//                    }
//                }
//            }
//        }
//        if (!commented) {
//            for (Traversable parent : removeMap.keySet()) {
//                removeSet = removeMap.get(parent);
//                for (Traversable child : removeSet) {
//                    parent.removeChild(child);
//                }
//            }
//        }
//    }
//
//    public void cleanAdditionalBarriers(Set<AnnotationStatement> barrSet) {
//        Tools.println("Number of barriers to be removed = " + barrSet.size(), 5);
//        for (AnnotationStatement astmt : barrSet) {
//            if (astmt != null) {
//                Traversable parent = astmt.getParent();
//                if (parent != null)
//                    parent.removeChild(astmt);
//                else
//                    Tools.println("[Error in cleanAdditionalBarriers()] parent is null!", 1);
//            }
//        }
//    }
//
}


