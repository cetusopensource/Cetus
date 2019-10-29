package ompd.hir;

import cetus.analysis.*;
import cetus.hir.*;

import java.util.*;

import ompd.hir.SectionSet.ELEMENT;
import ompd.hir.SectionSet.ERSD;
import ompd.hir.SectionSet.RSD;

public final class OMPDTools {


    private OMPDTools() {
    }

    /**
     * Returns a list of defined expressions in the traversable object t before the
     * occurance of Statement e .
     *
     * @param t the traversable object.
     * @return the list of defined expressions.
     */
    public static List<Expression> getDefListBeforeStatement(Traversable t, Statement e) {
        ArrayList<Expression> ret = new ArrayList<Expression>();

        if (t == null)
            return ret;

        // Add increment/decrement operator in search list.
        Set unary_def = new HashSet();
        unary_def.add("--");
        unary_def.add("++");
        unary_def.add("+=");
        unary_def.add("-=");
        unary_def.add("*=");
        unary_def.add("/=");

        DepthFirstIterator iter = new DepthFirstIterator(t);

        while (iter.hasNext()) {
            Object o = iter.next();
            if ((o).equals(e)) break;

            // Expression being modified
            if (o instanceof BinaryExpression) {
                if (o instanceof AssignmentExpression)
                    ret.add((AssignmentExpression) o);
                else {
                    BinaryExpression ex = (BinaryExpression) o;
                    if (ex.getParent() instanceof Initializer) {
//                        Initializer s = (Initializer)ex.getParent();
//                        VariableDeclarator vd = (VariableDeclarator)s.getParent();
//                        Expression ee=vd.getSymbol();
//                        /*FIXME: what about declarations that initializes declared variables*/
//                        //ret.add(ee);

                    }
                }
            } else if (o instanceof UnaryExpression) {
                UnaryExpression ue = (UnaryExpression) o;
                if (unary_def.contains(ue.getOperator().toString()))
                    ret.add(ue);
            }
        }

        return ret;
    }

    /**
     * Returns a set of defined symbols from the traversable object before Statement es.
     *
     * @param t the traversable object.
     * @return the set of defined symbols.
     */
    public static Set<Symbol> getDefSymbolBeforeStatement(Traversable t, Statement es) {
        Set<Symbol> ret = new HashSet<Symbol>();

        for (Expression e : getDefListBeforeStatement(t, es)) {
            Symbol symbol;
            if (e instanceof AssignmentExpression) {
                symbol = SymbolTools.getSymbolOf(((AssignmentExpression) e).getLHS());
            } else
                symbol = SymbolTools.getSymbolOf(e);
            if (symbol != null)
                ret.add(symbol);
        }

        return ret;
    }


    /**
     * find the coefficient expression of Symbol e in the IR tree t.
     * <p/>
     * example. findCoefficient(x+(2+j)*i , i) returns (2+j)
     */
    public static Expression findCoefficient(Traversable t, Symbol e) {
        DepthFirstIterator iter = new DepthFirstIterator(t);
        String e_string = e.toString(), exp_string;
        Expression t_exp, c_exp;


        if (!t.toString().contains(e_string)) return new IntegerLiteral(0);
        for (; ;) {
            try {
                t_exp = (Expression) iter.next(Expression.class);
            } catch (NoSuchElementException nse) {
                return null;
            }
            if (!(t_exp instanceof ArrayAccess) && t_exp.toString().contains(e_string)) break;
        }

        if (t_exp instanceof Identifier) {
            // for example a[i], stride=1
            return new IntegerLiteral(1);
        }

        while (t_exp instanceof BinaryExpression) {
            BinaryExpression tmp = (BinaryExpression) t_exp;
            if (tmp.getOperator().equals(BinaryOperator.ADD) || tmp.getOperator().equals(BinaryOperator.SUBTRACT)) {
                if (tmp.getLHS().toString().contains(e_string))
                    t_exp = tmp.getLHS();
                else
                    t_exp = tmp.getRHS();
            } else { // operators handled here are DIVIDE and MULTIPLY
                t_exp = IRTools.replaceSymbol(t_exp, e, new IntegerLiteral(1));
                return t_exp;
            }
        }
        if (t_exp instanceof Identifier) {
            // for example a[i], stride=1
            return new IntegerLiteral(1);
        }

        return null;
    }
    
    public static Expression getCoefficient(Expression e, Symbol index) {
    	
        Expression se = Symbolic.simplify(e);
        if(se.equals(index))
        	return new IntegerLiteral(1);
        if(!IRTools.containsSymbol(se, index))
        	return new IntegerLiteral(0);

        List<Expression> lst = Symbolic.getTerms(se);
        Expression factor = new IntegerLiteral(0);
        for(Expression exp:lst){
        	if(IRTools.containsSymbol(exp, index)){
        		factor = Symbolic.add(factor, IRTools.replaceSymbol(exp, index, new IntegerLiteral(1)));
        	}	
        }
        return factor;
    } 

    /**
     * Returns the set of Symbol that declared in the given Traversable st body code
     * including symbols declared in inner scopes
     * @param st the symbol table being searched.
     * @return the set of symbols.
     */
    public static Set<Symbol> getDeclaredSymbols(Traversable st)
    {
        Set ret = new HashSet<Symbol>();
        if ( st == null )
            return ret;

        DepthFirstIterator iter = new DepthFirstIterator(st);

        while ( iter.hasNext() )
        {
            Object o = iter.next();
            if ( (o instanceof VariableDeclarator) ){
                ret.add((Symbol)o);
            }
        }
        return ret;
    }
    
    /**
     * Returns true if Expression ar is nonlinear with respect to Symbol idx
     * TODO: Only tests for indirect accesses and accesses with function calls .. do the other cases
     */
    public static boolean isNonLinear(Expression ar, Symbol idx){
    	List<BinaryExpression> operators_lst = IRTools.getExpressionsOfType(ar, BinaryExpression.class);
    	for(BinaryExpression exp:operators_lst){
    		String op = exp.getOperator().toString();
    		if(op.equals("+") || op.equals("-") || op.equals("/") || op.equals("*")){
    			
    		}
    		else{
    			return true;
    		}
    		
    	}
		List<ArrayAccess> ac_lst = IRTools.getExpressionsOfType(ar, ArrayAccess.class);
		if(!ac_lst.isEmpty()){
			for(ArrayAccess ac: ac_lst)
				for(Symbol s:DataFlowTools.getUseSymbol(ac))
					if(idx.equals(s))
							return true;
		}
		List<FunctionCall> fc_lst = IRTools.getExpressionsOfType(ar, FunctionCall.class);
		if(!fc_lst.isEmpty()){
			for(FunctionCall fc: fc_lst)
				for(Symbol s:DataFlowTools.getUseSymbol(fc))
					if(idx.equals(s))
						return true;
		}
		return false;
	}

    /**
     * Returns a list of pragma annotations that are attached to annotatable
     * objects within the traversable object {@code t}.
     *
     * @param t the traversable object to be searched.
     * @param pragma_cls the type of pragmas to be searched for.
     * @return the list of matching pragma annotations.
     */
    public static <T extends PragmaAnnotation> List<T>
    collectPragmas(Traversable t, Class<T> pragma_cls) {
        List<T> ret = new LinkedList<T>();

        DepthFirstIterator iter = new DepthFirstIterator(t);
        while (iter.hasNext()) {
            Object o = iter.next();
            if (o instanceof Annotatable) {
                Annotatable at = (Annotatable) o;
                List<T> pragmas = at.getAnnotations(pragma_cls);
                ret.addAll(pragmas);
            }
        }
        return ret;
    }

    public static Set<DFANode> collectBarrierNodes(CFGraph cfg) {
        Set<DFANode> nodes = new HashSet<DFANode>();

        Iterator<DFANode> iter = cfg.iterator();
        while (iter.hasNext()) {
            DFANode node = iter.next();
            if (isBarrierNodeButNotFromSerialToParallel(node)) {
                nodes.add(node);
            }
        }

        return nodes;
    }


    public static boolean isBarrierNodeButNotFromSerialToParallel(DFANode node) {
        String tag = (String) node.getData("tag");
        String type = (String) node.getData("type");
        if (tag != null && tag.equals("barrier")) {
            if (type != null && !type.equals("S2P")) return true;
        }
        return false;
    }

    /**
     * This function generates an array[index] expression.
     * @param array usually ompd_lb# or ompd_ub#
     * @param index usually ompd_i or ompd_procid
     * @return the array access expression
     */
    public static Expression createArrayAccess(Symbol array, Symbol index) {
        Identifier identifier = new Identifier(array);
        ArrayAccess arrayAccess = new ArrayAccess(identifier, new Identifier(index));
        return arrayAccess;
    }

    public static Set<Symbol> getUseSymbols(Section section) {
        Set<Symbol> symbols = new HashSet<Symbol>();

        for (Section.ELEMENT element: section) {
            for (Expression expression : element) {
                Set<Symbol> candidates = DataFlowTools.getUseSymbol(expression);
                for (Symbol candidate : candidates) {
                    if (!candidate.getSymbolName().equals("ompd_i"))
                        symbols.add(candidate);
                }
            }
        }

        return symbols;
    }



    public static Statement findParallelStatement(Traversable t) {
        while (t != null && !(t instanceof Procedure)) {
            if (!IRTools.collectPragmas(t, OmpdAnnotation.class, "parallel").isEmpty())
                return (Statement)t;

            t = t.getParent();
        }

        return null;
    }

    public static Set<Symbol> getSharedVariables(Traversable t) {
        Set<Symbol> ret = new HashSet<Symbol>();

        List<OmpdAnnotation>annotations = IRTools.collectPragmas(t, OmpdAnnotation.class, "shared");

        for (OmpdAnnotation annotation : annotations) {
            Set<Symbol> shared_set = annotation.get("shared");
            if (shared_set == null) {
                Tools.exit("[ERROR] omp shared construct has null shared set");
            }
            else {
                ret.addAll(shared_set);
            }
        }
        return ret;
    }


    public static Set<Symbol> getSharedArrays(Set<Symbol> shared_vars) {
        Set<Symbol> set = new HashSet<Symbol>();
        for (Symbol symbol : shared_vars) {
            if (SymbolTools.isArray(symbol)) set.add(symbol);
        }
        return set;
    }

    public static Set<Symbol> getSharedArrays(Traversable t) {
        Set<Symbol> shared_vars = getSharedVariables(t);
        Set<Symbol> set = new HashSet<Symbol>();
        for (Symbol symbol : shared_vars) {
            if (SymbolTools.isArray(symbol)) set.add(symbol);
        }
        return set;
    }

    public static Procedure findMain(Program program) {
        List<Procedure> procedures = IRTools.getProcedureList(program);

        for (Procedure procedure : procedures) {
            if (procedure.getName().toString().equals("main"))
                return procedure;
        }

        return null;
    }

    public static Set<ArrayAccess> collectArrayAccesses(Traversable t, Symbol symbol) {
        List<ArrayAccess> allAccesses = IRTools.getDescendentsOfType(t, ArrayAccess.class);
        Set<ArrayAccess> result = new HashSet<ArrayAccess>();

        for (ArrayAccess arrayAccess : allAccesses) {
            if (arrayAccess.getArrayName().toString().equals(symbol.getSymbolName()))
                result.add(arrayAccess);
        }

        return result;
    }

    public static Statement getZerothStatement(CompoundStatement compoundStatement) {
        Statement position = IRTools.getLastDeclarationStatement(compoundStatement);
        if (position != null)
            return position;

        List<Traversable> children = compoundStatement.getChildren();
        if (children.size() == 0) {
            /* empty body. Let's add an annotation statement */
            OmpdAnnotation annotation = new OmpdAnnotation("first_stmt", null);
            AnnotationStatement annotationStatement = new AnnotationStatement(annotation);
            compoundStatement.addStatement(annotationStatement);
            return annotationStatement;
        } else {
            Statement firstStatement = (Statement) children.get(0);

            if (firstStatement.getAnnotation(OmpdAnnotation.class, "first_stmt") != null) {
                return firstStatement;
            } else {
                OmpdAnnotation annotation = new OmpdAnnotation("first_stmt", null);
                AnnotationStatement annotationStatement = new AnnotationStatement(annotation);
                compoundStatement.addStatementBefore(firstStatement, annotationStatement);
                return annotationStatement;
            }
        }
    }

    public static ForLoop getOuterLoopWithoutUsingSymbols(Statement statement, Set<Symbol> symbols) {
        ForLoop forLoop = null, candidate;

        candidate = IRTools.getAncestorOfType(statement, ForLoop.class);

        while (candidate != null) {
            boolean found = false;
            Set<Symbol> useSymbols = DataFlowTools.getUseSymbol(candidate);

            for (Symbol symbol : symbols) {
                if (useSymbols.contains(symbol)) {
                    return forLoop;
                }
            }

            /* okay, the candidate loop does not contain any uses of the given symbols.
               Let's keep this loop, and look further.
             */
            forLoop = candidate;
            candidate = IRTools.getAncestorOfType(candidate, ForLoop.class);
        }

        return forLoop;
    }

    public static Set<Symbol> collectLoopBoundArraySymbols(Traversable input_code) {
        Set<Symbol> result = new HashSet<Symbol>();

        List<ForLoop> forLoops = IRTools.getDescendentsOfType(input_code, ForLoop.class);

        for (ForLoop forLoop : forLoops) {
            Expression lowerBoundExpression = LoopTools.getLowerBoundExpression(forLoop);
            if (lowerBoundExpression != null) {
                result.addAll(DataFlowTools.getUseSymbol(lowerBoundExpression));
            }

            Expression upperBoundExpression = LoopTools.getUpperBoundExpression(forLoop);
            if (upperBoundExpression != null) {
                result.addAll(DataFlowTools.getUseSymbol(upperBoundExpression));
            }
        }

        /* Let's remove symbols whose type is not array. */
        Set<Symbol> remove = new HashSet<Symbol>();
        for (Symbol symbol : result) {
            if (symbol.getArraySpecifiers().isEmpty()) {
                remove.add(symbol);
            }
        }

        result.removeAll(remove);

        return result;
    }

    /**
     * Returns a set of defined symbols from the traversable object.
     *
     * @param t the traversable object.
     * @return the set of defined symbols.
     */
    public static Set<Symbol> getDefSymbol(Traversable t)
    {
        Set<Symbol> ret = DataFlowTools.getDefSymbol(t);

        if (t instanceof VariableDeclarator) {
            ret.add((Symbol)t);
        }

        return ret;
    }
    
    /**
     * Returns 1 if loop stirde is increasing, -1 if loop stride is decreasing, 0 if unknown direction.
     */
    public static int getLoopDirection(ForLoop loop, RangeDomain rd1){
    	RangeDomain rd;
    	if(rd1==null)
    		rd= new RangeDomain();
    	else
    		rd=rd1;
    	Expression strd = LoopTools.getIncrementExpression(loop);
    	if(strd==null || strd.equals(new IntegerLiteral(0)))
    		return 0;
    	 Relation rel = rd.compare(strd,new IntegerLiteral(0));
    	 if(rel.isUnknown())
    		 return 0;
    	 if(rel.isLT())
    		 return -1;
    	 else
    		 return 1;
    	
    /*	
   	 if(strd instanceof UnaryExpression){
   		 if(((UnaryExpression)strd).getOperator().toString().startsWith("--"))
   			 direction=-1;
   		 else if(((UnaryExpression)strd).getOperator().toString().startsWith("++"))
   			 direction=1;
   	 }
   	 else if(strd instanceof AssignmentExpression){
   		 AssignmentOperator op = ((AssignmentExpression)strd).getOperator();
   		 Expression right = ((AssignmentExpression)strd).getRHS();
   		 if(op.equals(AssignmentOperator.NORMAL))
   			 right=Symbolic.simplify(IRTools.replaceSymbol(right, LoopTools.getLoopIndexSymbol((ForLoop)loop), LoopTools.getLowerBoundExpression((ForLoop)loop)));
   		 if(OMPDTools.isNonLinear(right,LoopTools.getLoopIndexSymbol((ForLoop)loop)))
				 Tools.exit("ERROR in addRangeDomainToCFG() in SPMDizer: Unsupported Stride Expression");
   		 Relation rel = rd.compare(right,new IntegerLiteral(0));
   		 if(rel.isUnknown()){
   			 Tools.exit("ERROR in addRangeDomainToCFG() in SPMDizer: Unknwon Stride direction");
   		 }
   		 else{
   			 if(op.toString().equals("-=")){
   				 if(rel.isGE())
   					 direction=-1;
   				 else
   					 direction=1;
   			 }
   			 else{
   				if(rel.isGE())
   					direction=1;
   				else
   					direction=-1;
   			 }
   		 }
   	 }
   	 */
    	
    }
    
    /**
     * Returns 1 if positiveg, -1 if negative, 0 if unknown.
     */
    
    public static int expression_sign(Expression expr, RangeDomain rd1){
		Relation stride_rel;
		RangeDomain rd;
		if(rd1==null)
			rd=new RangeDomain();
		else
			rd=rd1;
		stride_rel = rd.compare(expr, new IntegerLiteral(0));
		if(stride_rel.isUnknown())
			return 0;
		if(stride_rel.isLT())
			return -1;
		else
			return 1;
	}
    
    public static boolean do_both_have_same_partitioned_dimension(SectionSet.SECTION a, SectionSet.SECTION b, RangeDomain rd){
    	if( a.get_parallel_dim()==b.get_parallel_dim() && 
				 (
				    (a.isRSD() && b.isRSD() && ELEMENT.isEqual(((RSD)a).get(a.get_parallel_dim()), ((RSD)b).get(b.get_parallel_dim()), rd)) ||
				    (a.isRSD() && b.isERSD() && ELEMENT.isEqual(((RSD)a).get(a.get_parallel_dim()), ((ERSD)b).get(0).get(b.get_parallel_dim()), rd)) ||
				    (a.isERSD() && b.isRSD() && ELEMENT.isEqual(((ERSD)a).get(0).get(a.get_parallel_dim()), ((RSD)b).get(b.get_parallel_dim()), rd)) ||
				    (a.isERSD() && b.isERSD() && ELEMENT.isEqual(((ERSD)a).get(0).get(a.get_parallel_dim()), ((ERSD)b).get(0).get(b.get_parallel_dim()), rd))
				 )
		  ){ 
			return true;
		 }
		 else{
			 return false;
		 }
    }
    
  
    
    

    public static void criticalError(String msg, int errorCode) {
        System.out.println(msg);
        System.exit(errorCode);
    }

    public static void criticalError(String msg) {
        System.out.println(msg);
        System.exit(-1);
    }

}
