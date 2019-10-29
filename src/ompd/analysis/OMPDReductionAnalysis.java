package ompd.analysis;

import static cetus.hir.PrintTools.println;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.TreeMap;

import ompd.hir.OmpdAnnotation;
import ompd.transforms.ProgramRecord;

import cetus.analysis.DFANode;
import cetus.analysis.RangeDomain;
import cetus.analysis.Reduction;
import cetus.analysis.Section;
import cetus.hir.*;

public class OMPDReductionAnalysis {
	
	 private ProgramRecord prog_record;
	 private Program program;
	 Reduction reduce_pass;
	 
	 public OMPDReductionAnalysis(ProgramRecord rcd){
		 this.prog_record = rcd;
		 program = rcd.get_program();
		 reduce_pass = new Reduction(program);
	 }
	 
	 public void start(TranslationUnit tu, Procedure proc){
		 performReductionAnalysisInProcedure(proc,prog_record.get_PCFGraph(tu, proc)); 
	 }
	 
	 private void performReductionAnalysisInProcedure(Procedure mainProc, PCFGraph cfg){
	     

	        convertAtomicsToCriticalSections(mainProc);
	        

	       
	        convertCS(mainProc, cfg);
	       
	        
	        /* generate ompd_allreduce */
	 
	        convertOmpReduction(mainProc);
	       
	 }
	 
	   /* It converts a serial loop that contains only atomic statement into a
	     * critical section that has the serial loop without "omp atomic" annotation
	     * in order to make it compatible with the conversion from critical section
	     * to allreduce call. Scalar type of atomic statement is also considered. */
	    private void convertAtomicsToCriticalSections(Procedure proc) {
	        List<OmpdAnnotation> ompdAnnotations = IRTools.collectPragmas(proc, OmpdAnnotation.class, "atomic");

	        println("convertAtomicsToCriticalSections() ->", 2);

	        for (OmpdAnnotation annotation : ompdAnnotations) {
	            Statement atomicStatement = (Statement) annotation.getAnnotatable();
	            convertAtomicToCritical(atomicStatement);
	        }
	        println("<- convertAtomicsToCriticalSections()", 2);
	    }

	    private void convertAtomicToCritical(Statement atomicStatement) {
	        /* check it is inside of a loop */
	        ForLoop forLoop = IRTools.getAncestorOfType(atomicStatement, ForLoop.class);
	        if (forLoop == null)
	            return;

	        /* check the loop is a serial loop. */
	        OmpdAnnotation annotation = forLoop.getAnnotation(OmpdAnnotation.class, "for");
	        if (annotation != null)
	            return;

	        /* check the atomic statement is only the statement except for annotation statements. */
	        CompoundStatement compoundStatement = (CompoundStatement)forLoop.getBody();
	        FlatIterator iterator = new FlatIterator(compoundStatement);

	        while (iterator.hasNext()) {
	            Statement statement = (Statement)iterator.next();
	            if (statement != atomicStatement && !(statement instanceof AnnotationStatement)) {
	                return;
	            }
	        }

	        /* It is eligible to elevate atomic operation on the statement to critical section
	         * outside of the serial for loop. */
	        OmpdAnnotation atomicAnnotation = atomicStatement.getAnnotation(OmpdAnnotation.class, "atomic");
	        atomicAnnotation.detach();
	        OmpdAnnotation criticalAnnotation = new OmpdAnnotation("critical", "true");
	        forLoop.annotate(criticalAnnotation);
	        PrintTools.println("atomic to critical, stmt = " + atomicStatement, 0);
	     }

	    /**
	     * convertCS
	     */
	    private void convertCS(Procedure proc, PCFGraph cfg) {
	        List<OmpdAnnotation> alist = IRTools.collectPragmas(proc, OmpdAnnotation.class, "critical");
	        Map<String, Set<Expression>> reduce_map;

	        println("convertCS() ->", 2);

	        for (OmpdAnnotation ca : alist) {
	            Statement cs_stmt = (Statement) ca.getAnnotatable();

	            Set<Symbol> shared_vars;

	            // get a set of shared variables
	            {
	                // find the parent parallel statement of this current critical section
	                Traversable tr = (Statement) cs_stmt.getParent();
	                while (true) {
	                    //println("tr :" +tr, 0);
	                    if (tr instanceof Procedure) {
	                        println("cs_stmt: " + cs_stmt, 0);
	                        Tools.exit("[convertCS] CS is not inside the parent parallel region");
	                    }
	                    else if (!IRTools.collectPragmas(tr, OmpdAnnotation.class, "parallel").isEmpty()) {
	                        break;
	                    }
	                    tr = tr.getParent();
	                }

	                Statement parallel_stmt = (Statement) tr;
	                // shared variables used in the parent parallel region
	                shared_vars = parallel_stmt.getAnnotation(OmpdAnnotation.class, "shared").get("shared");
	            }
	            
	            // --------------------------------------------------------------------------------
	            // Perform reduction recognition to find reduction variables in the critical section
	            // --------------------------------------------------------------------------------
	            if (cs_stmt instanceof ForLoop) {
	                /* omp critical is attached to a for loop, but reduce_pass thinks that
	                 * a reduction operation in a for loop has self-carried dependence and
	                 * returns an empty map. Because we know that the for loop is used for array
	                 * reduction, passing the body of the for loop gets a correct non-empty
	                 * reduce map from it. */
	                reduce_map = reduce_pass.analyzeStatement(((ForLoop) cs_stmt).getBody());
	            } else {
	                reduce_map = reduce_pass.analyzeStatement(cs_stmt);
	            }

	            if (reduce_map.isEmpty()) continue;

	            // find shared/private def variables in the critical section
	            Set<Expression> private_def_set = new HashSet<Expression>();
	            Set<Expression> shared_def_set = new HashSet<Expression>();
	            Set<Expression> all_def_set = DataFlowTools.getDefSet(cs_stmt);
	            for (Expression expr : all_def_set) {
	                Symbol def_symbol = SymbolTools.getSymbolOf(expr);
	                if (def_symbol == null) {
	                    PrintTools.println("def_symbol is null", 0);
	                } else if (def_symbol.getSymbolName() == null) {
	                    PrintTools.println("def_symbol.getSymbolName() is null", 0);
	                }
	                
	                boolean is_shared = false;
	                for (Symbol shared_var : shared_vars) {
	                    if (shared_var == null) {
	                        PrintTools.println("shared_var is null", 0);
	                    } else if (shared_var.getSymbolName() == null) {
	                        PrintTools.println("shared_var.getSymbolName() is null", 0);
	                    }

	                    if (shared_var.getSymbolName().equals(def_symbol.getSymbolName())) {
	                        is_shared = true;
	                        break;
	                    }
	                }
	                if (is_shared)
	                    shared_def_set.add(expr);
	                else
	                    private_def_set.add(expr);
	            }

	            println("shared_def_set  = " + shared_def_set, 2);
	            println("private_def_set = " + private_def_set, 2);

	            if (shared_def_set.isEmpty()) {
	                println("ConvertCS(): critical section exists but no shared variables found", 0);

	                // remove the critical section Annotation and do not generate communication
	            }
	            else {
	                boolean all_reductions = true;
	                for (Expression expr : shared_def_set)        // for each shared def variable
	                {
	                    boolean is_reduction = false;
	                    for (String op : reduce_map.keySet()) {
	                        for (Expression red_expr : reduce_map.get(op)) {
	                            if (expr.toString().equals(red_expr.toString())) {
	                                println(expr.toString() + " is used in reduction", 2);
	                                is_reduction = true;
	                                break;
	                            }
	                            else {
	                                println(expr.toString() + " is not used in reduction", 2);
	                            }
	                        }
	                    }
	                    if (is_reduction == false) {
	                        all_reductions = false;
	                        break;
	                    }
	                }

	                // if all shared data modified in the CS are reductions, then convert it to a reduction form
	                if (all_reductions) {
	                    println("All shared def variables are used in reduction", 2);

	                    println(cs_stmt.toString(), 2);

	                    // reduction statement -> allreduce function call.

	                    for (String reduce_op : reduce_map.keySet()) {
	                        for (Expression red_expr : reduce_map.get(reduce_op)) {
	                        	PrintTools.println("Reduction operation  = " + reduce_op, 0);
	                        	PrintTools.println("Reduction expression = " + red_expr, 0);
	                            Statement red_stmt = red_expr.getStatement();
	                            Symbol red_symbol = SymbolTools.getSymbolOf(red_expr);
	                            Expression inc_expr = getIncrement(red_expr);
	                            Symbol inc_symbol = SymbolTools.getSymbolOf(inc_expr);
	                            Expression inc_saddr = null, red_saddr = null, red_size = null;
	                            if (red_expr instanceof ArrayAccess && inc_expr instanceof ArrayAccess) {
	                                RangeDomain rd = get_range(cfg,red_stmt); //(RangeDomain) range_map.get(red_stmt);
	                                Section.MAP def_map = DataFlowTools.getDefSectionMap(red_expr, rd, DataFlowTools.getDefSymbol(cs_stmt));
	                                Section section = def_map.get(red_symbol);
	                                assert section.size() == 1 : "size of section must be one!";
	                                Section.ELEMENT range_list = section.get(0);
	                                assert range_list.size() == 1 : "size of range_list must be one!";
	                                Expression range_expr = range_list.get(0);
	                                if (range_expr instanceof RangeExpression) {
	                                    Expression lb_expr = ((RangeExpression) range_expr).getLB();
	                                    Expression ub_expr = ((RangeExpression) range_expr).getUB();

	                                    Identifier inc_id = new Identifier(inc_symbol);
	                                    ArrayAccess inc_array = new ArrayAccess(inc_id, lb_expr.clone());
	                                    inc_saddr = new UnaryExpression(UnaryOperator.ADDRESS_OF, inc_array);

	                                    Identifier red_id = new Identifier(red_symbol);
	                                    ArrayAccess red_array = new ArrayAccess(red_id, lb_expr.clone());
	                                    red_saddr = new UnaryExpression(UnaryOperator.ADDRESS_OF, red_array);

	                                    Expression tmp_size = Symbolic.subtract(ub_expr, lb_expr);
	                                    red_size = Symbolic.add(tmp_size, new IntegerLiteral(1));
	                                }
	                                else
	                                    Tools.exit("[convertCS] not supported range: " + range_expr);
	                            }
	                            else    // scalar variables
	                            {
	                                Identifier inc_id = new Identifier(inc_symbol);
	                                inc_saddr = new UnaryExpression(UnaryOperator.ADDRESS_OF, inc_id);

	                                //Identifier red_id = new Identifier(red_symbol.getSymbolName());
	                                //red_saddr = new UnaryExpression(UnaryOperator.ADDRESS_OF, red_id);
	                                red_saddr = new UnaryExpression(UnaryOperator.ADDRESS_OF, red_expr.clone());
	                                red_size = new IntegerLiteral(1);
	                            }

	                            {
	                                String oper;
	                                // add argument MPI_Op: MPI_PROD or MPI_SUM
	                                if (reduce_op.equals("+") || reduce_op.equals("-"))
	                                    oper = "MPI_SUM";
	                                else if (reduce_op.equals("*"))
	                                    oper = "MPI_PROD";
	                                else
	                                    oper = "MPI_???";

	                                String code_str = "ompd_allreduce(" + inc_saddr + ", " + red_saddr + ", "
	                                    + red_size + ", " + getMPIType(red_symbol) + ", " + oper + ");";
	                                CodeAnnotation code_annot = new CodeAnnotation(code_str);
	                                AnnotationStatement as = new AnnotationStatement(code_annot);
	                                ((CompoundStatement) (cs_stmt.getParent())).addStatementAfter(cs_stmt, as);
	                                //OMPDTimer.encloseByTimerCode(as, OMPDTimer.ALLREDUCE);
	                            }
	                        }
	                    }

	                    // remove AnnotationStatement, "#pragma cetus critical", attached to this CS
	                    ca.detach();

	                    // Currently, "#pragma omp critical" cannot be deleted because it is a DeclarationStatement,
	                    // which is not attached to this critical section

	                    // Now, we remove CS
	                    cs_stmt.detach();
	                }
	                else {
	                    Tools.exit("ERROR in ConvertCS(): Unsupported type of critical section: not all reductions");
	                }
	            }
	        }

	        println("<- ConvertCS()", 2);
	    }
	    
	    private Expression getIncrement(Expression reduce_expr) {
	        Expression top_expr = (Expression) reduce_expr.getParent();
	        Expression increment = null;
	        if (top_expr instanceof UnaryExpression)            // inc++; or dec--;
	        {
	            UnaryOperator unary_op = ((UnaryExpression) top_expr).getOperator();
	            if (unary_op == UnaryOperator.PRE_INCREMENT || unary_op == UnaryOperator.POST_INCREMENT) {
	                increment = new IntegerLiteral(1);
	            }
	            else if (unary_op == UnaryOperator.PRE_DECREMENT || unary_op == UnaryOperator.POST_DECREMENT) {
	                increment = new IntegerLiteral(-1);
	            }
	        }
	        else if (top_expr instanceof AssignmentExpression) {
	            AssignmentOperator assign_op = ((AssignmentExpression) top_expr).getOperator();
	            Expression lhse = ((AssignmentExpression) top_expr).getLHS();
	            Expression rhse = ((AssignmentExpression) top_expr).getRHS();
	            if (assign_op == AssignmentOperator.NORMAL) {        // sum = sum + <...>;
	                Expression simplified_rhse = Symbolic.simplify(rhse);
	                Expression lhse_in_rhse = IRTools.findExpression(simplified_rhse, lhse);
	                Expression rhs_parent_expr = (Expression) (lhse_in_rhse.getParent());    // sum + <...>
	                assert rhs_parent_expr instanceof BinaryExpression : "rhs_parent_expr must be BinaryExpression!";
	                if (rhs_parent_expr instanceof BinaryExpression) {
	                    String reduce_op = ((BinaryExpression) rhs_parent_expr).getOperator().toString();
	                    if (reduce_op.equals("+"))
	                        increment = Symbolic.subtract(rhse, lhse);
	                    else if (reduce_op.equals("*"))
	                        increment = Symbolic.divide(rhse, lhse);
	                    else
	                        Tools.exit("[getIncrement] not supported reduce operator: " + reduce_op);
	                }
	                else
	                    Tools.exit("[getIncrement] not supported reduce form: " + top_expr);
	            }
	            else if (assign_op == AssignmentOperator.ADD || assign_op == AssignmentOperator.SUBTRACT) {        // sum += <...>; or sum -+ <...>;
	                increment = Symbolic.simplify(rhse);
	            }
	            else if (assign_op == AssignmentOperator.MULTIPLY) {        // sum *= <...>;
	                increment = Symbolic.simplify(rhse);
	            }
	        }

	        assert increment != null : "increment should not be null";
	        return increment;
	    }
	    
	    private Identifier getMPIType(Symbol symbol) {
	        List<Specifier> type_specs = symbol.getTypeSpecifiers();
	        String id = type_specs.get(0).toString();

	        for (; ;) {
	            String type = null;
	            boolean signed = false;

	            for (Specifier spec : type_specs) {
	                if (spec.toString().equals("signed")) {
	                    signed = true;
	                    break;
	                }
	            }

	            for (Specifier spec : type_specs) {
	                String spec_str = spec.toString();
	                if (spec_str.equals("char")) {
	                    type = signed ? "MPI_SIGNED_CHAR" : "MPI_UNSIGNED_CHAR";
	                }
	                else if (spec_str.equals("short")) {
	                    type = signed ? "MPI_SHORT" : "MPI_UNSIGNED_SHORT";
	                }
	                else if (spec_str.equals("int")) {
	                    type = signed ? "MPI_INT" : "MPI_UNSIGNED";
	                }
	                else if (spec_str.equals("long")) {
	                    type = signed ? "MPI_LONG" : "MPI_UNSIGNED_LONG";
	                }
	                else if (spec_str.equals("float")) {
	                    type = "MPI_FLOAT";
	                }
	                else if (spec_str.equals("double")) {
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
	            try {
	                // Get the original type of this user-defined type
	                type_specs = findTypedefSpecifiers(id);
	            } catch (NullPointerException e) {
	                return null;
	            }
	        }
	    }
	    
	    private List<Specifier> findTypedefSpecifiers(String str) {
	        DepthFirstIterator iter = new DepthFirstIterator(program);
	        iter.pruneOn(VariableDeclaration.class);

	        println("findTypedefDeclaration(" + str + ")", 2);

	        for (; ;) {
	            try {
	                VariableDeclaration decl = (VariableDeclaration) iter.next(VariableDeclaration.class);

	                if (decl.isTypedef()) {
	                    List<Specifier> specs = decl.getSpecifiers();

	                    // Dump the list
	                    println(decl.toString(), 2);

	                    List<IDExpression> symbolList = getDeclaredSymbols(decl);
	                    for (IDExpression id : symbolList)
	                        if (id.getName().equals(str))
	                            return decl.getSpecifiers();
	                }

	            } catch (NoSuchElementException e) {
	                println("->Not found", 2);
	                return null;
	            }
	        }
	    }
	    
	    private List<IDExpression> getDeclaredSymbols(VariableDeclaration decl) {
	        int i;
	        ArrayList<IDExpression> list = new ArrayList<IDExpression>();
	        for (i = 0; i < decl.getNumDeclarators(); i++) {
	            Declarator declarator;
	            declarator = decl.getDeclarator(i);
	            list.add(declarator.getID());
	        }

	        return list;
	    }
	    
	    // generate ompd_allreduce() for #pragma cetus reduction(+:...)
	    private void convertOmpReduction(Procedure proc) {
	        Map<String, Set<String>> reduction_map;
	        List<OmpdAnnotation> alist = IRTools.collectPragmas(proc, OmpdAnnotation.class, "reduction");

	        for (OmpdAnnotation ca : alist) {
	            Statement reduce_loop_stmt = (Statement) ca.getAnnotatable();
	            CompoundStatement curr_parent = (CompoundStatement) reduce_loop_stmt.getParent();
	            reduction_map = ca.get("reduction");
	            SymbolTable stable = IRTools.getAncestorOfType(reduce_loop_stmt, SymbolTable.class);

	            /*
	            if (reduction_map == null) Tools.exit("reduction_map is null in convertOmpReduction");
	            if (reduction_map.keySet() == null) Tools.exit("reduction_map.ketSet() is null");
	             */

	            for (String op : reduction_map.keySet()) {
	                for (String lhs_name : reduction_map.get(op)) {
	                    Symbol lhs_symbol = SymbolTools.getSymbolOfName(lhs_name, curr_parent);
	                    Identifier lhs_id = new Identifier(lhs_symbol);
	                    if (lhs_symbol != null) {
	                        println("sum_symbol: " + lhs_symbol.getSymbolName(), 3);
	                    }
	                    else {
	                        println("lhs_symbol is not found: lhs_name = " + lhs_name, 3);
	                    }

	                    // -----------------------------------------------------------------
	                    // create a private variable, l_sum, intialize it, and declare it
	                    // -----------------------------------------------------------------
	                    String new_lhs_name = "l_" + lhs_name;
	                    IDExpression new_lhs_id;
	                    Symbol new_lhs_symbol;

	                    new_lhs_symbol = SymbolTools.getSymbolOfName(new_lhs_name, curr_parent);

	                    if (new_lhs_symbol == null) {
	                        // Declaration of l_sum_id can exist already, if multiple loops
	                        // for reduction use the same reduction variable.
	                        new_lhs_id = new NameID(new_lhs_name);
	                        Declarator new_lhs_declarator = new VariableDeclarator(new_lhs_id);

	                        // l_sum_spec_list copies all specifiers of whom extern keyword may reside,
	                        // so remove "extern" keyword from them.
	                        List<Specifier> l_sum_spec_list = new ArrayList<Specifier>();
	                        l_sum_spec_list.addAll(lhs_symbol.getTypeSpecifiers());
	                        l_sum_spec_list.remove(Specifier.EXTERN);
	                        Declaration l_sum_decl = new VariableDeclaration(l_sum_spec_list, new_lhs_declarator);
	                        curr_parent.addDeclaration(l_sum_decl);
	                    }
	                    else {
	                        println("Declaration of new_lhs_name(" + new_lhs_name + ") already exists", 3);
	                        new_lhs_id = new Identifier(new_lhs_symbol);
	                    }
	                    //------------------------------------------------------------------
	                    // insert initialization code before reduction loop
	                    // e.g.) l_sum = 0;
	                    //------------------------------------------------------------------
	                    {
	                        String code_str = new_lhs_name + " = " + getInitialValue(lhs_symbol, op) + ";";
	                        //String code_str = new_lhs_name + " = " + lhs_name + ";";
	                        CodeAnnotation code = new CodeAnnotation(code_str);
	                        AnnotationStatement as = new AnnotationStatement(code);
	                        curr_parent.addStatementBefore(reduce_loop_stmt, as);
	                    }
	                    // -----------------------------------------------------------------
	                    // replace reduction variable, sum, with l_sum
	                    // -----------------------------------------------------------------
	                    IRTools.replaceAll(reduce_loop_stmt, lhs_id, new_lhs_id);

	                    // -----------------------------------------------------------------
	                    // Insert ompd_allreduce( void *sendbuf, void *recvbuf, int count,
	                    //                        MPI_Datatype datatype, MPI_Op op )
	                    // -----------------------------------------------------------------
	                    {
	                        String op_str;
	                        if (op.equals("+") || op.equals("-")) {
	                            op_str = "MPI_SUM";
	                        }
	                        else if (op.equals("*")) {
	                            op_str = "MPI_PROD";
	                        }
	                        else {
	                            op_str = "MPI_???";
	                            Tools.exit("convertOmpReduction: unsupported reduction type" + op);
	                        }

	                        /*String code_str = "ompd_allreduce(&" + new_lhs_name + ", &" + lhs_name + ", 1, " +
	                            getMPIType(lhs_symbol) + ", " + op_str + ");";*/
	                        String code_str = "ompd_allreduce(&" + new_lhs_name + ", &" + new_lhs_name + ", 1, " +
		                            getMPIType(lhs_symbol) + ", " + op_str + ");";
	                        CodeAnnotation code = new CodeAnnotation(code_str);
	                        AnnotationStatement as = new AnnotationStatement(code);
	                        // TODO: Check whether it is a good place to insert the reduction statement.
	                        curr_parent.addStatementAfter(reduce_loop_stmt, as);
	                        
	                        ExpressionStatement exp_st = new ExpressionStatement(new AssignmentExpression(lhs_id.clone(),AssignmentOperator.ADD,new_lhs_id.clone()));
	                        curr_parent.addStatementAfter(as, exp_st);
	                        
	                        //OMPDTimer.encloseByTimerStatement(as, OMPDTimer.ALLREDUCE);
	                    }
	                }
	            }
	        }
	    }
	    
	    private Expression getInitialValue(Symbol symbol, String reduce_op) {
	        Expression expr = null;
	        String type = getMPIType(symbol).getName();

	        if (reduce_op.equals("+") || reduce_op.equals("-")) {
	            if (type.equals("MPI_SHORT") || type.equals("MPI_UNSIGNED_SHORT") ||
	                type.equals("MPI_INT") || type.equals("MPI_UNSIGNED") ||
	                type.equals("MPI_LONG") || type.equals("MPI_UNSIGNED_LONG")) {
	                expr = new IntegerLiteral(0);
	            }
	            else if (type.equals("MPI_FLOAT") || type.equals("MPI_DOUBLE")) {
	                expr = new FloatLiteral(0.0);
	            }
	            else {
	                Tools.exit("[getInitialValue] unsupported type: " + type + " " + symbol.getSymbolName());
	            }
	        }
	        else if (reduce_op.equals("*")) {
	            if (type.equals("MPI_SHORT") || type.equals("MPI_UNSIGNED_SHORT") ||
	                type.equals("MPI_INT") || type.equals("MPI_UNSIGNED") ||
	                type.equals("MPI_LONG") || type.equals("MPI_UNSIGNED_LONG")) {
	                expr = new IntegerLiteral(1);
	            }
	            else if (type.equals("MPI_FLOAT") || type.equals("MPI_DOUBLE")) {
	                expr = new FloatLiteral(1.0);
	            }
	            else {
	                Tools.exit("[getInitializer] unsupported type: " + type + " " + symbol.getSymbolName());
	            }
	        }
	        return expr;
	    }
	    
	    private RangeDomain get_range(PCFGraph cfg, Statement stmt){
	    	RangeDomain rd=null;
	    	TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
			 Iterator<DFANode> iter = cfg.iterator();
		     while (iter.hasNext()) {
		            DFANode node = iter.next();
		            node_list.put((Integer) node.getData("top-order"), node);
		     }
		     for (Integer order : node_list.keySet()) {
		            DFANode node = node_list.get(order);
		            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
		            if(ir!=null && ir.equals(stmt)){
		            	rd = (RangeDomain) node.getData("range_out");
		            	break;
		            }
		     }
		     if(rd==null)
		    	 rd = new RangeDomain();
	    	return rd;
	    }


}
