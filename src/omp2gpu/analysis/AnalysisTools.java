package omp2gpu.analysis;

import java.util.Arrays;
import java.util.Collections;
import java.util.Collection; 
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.LinkedList;

import omp2gpu.hir.CudaAnnotation;
import omp2gpu.hir.CUDASpecifier;
import omp2gpu.hir.CudaStdLibrary;
import omp2gpu.hir.KernelFunctionCall;
import omp2gpu.transforms.SplitOmpPRegion;

import cetus.analysis.CFGraph;
import cetus.analysis.DFAGraph;
import cetus.analysis.DFANode;
import cetus.analysis.RangeDomain;
import cetus.analysis.Section;
import cetus.analysis.Section.ELEMENT;
import cetus.analysis.Section.MAP;
import cetus.exec.Driver;
import cetus.hir.AccessExpression;
import cetus.hir.AccessSymbol;
import cetus.hir.Annotatable;
import cetus.hir.AnnotationStatement;
import cetus.hir.ArrayAccess;
import cetus.hir.CompoundStatement;
import cetus.hir.ClassDeclaration;
import cetus.hir.Declaration;
import cetus.hir.Declarator;
import cetus.hir.DepthFirstIterator;
import cetus.hir.Expression;
import cetus.hir.ForLoop;
import cetus.hir.FunctionCall;
import cetus.hir.IDExpression;
import cetus.hir.Literal;
import cetus.hir.NestedDeclarator;
import cetus.hir.OmpAnnotation;
import cetus.hir.PragmaAnnotation;
import cetus.hir.Procedure;
import cetus.hir.ProcedureDeclarator;
import cetus.hir.PointerSpecifier;
import cetus.hir.PseudoSymbol;
import cetus.hir.StandardLibrary;
import cetus.hir.Statement;
import cetus.hir.Symbol;
import cetus.hir.Tools;
import cetus.hir.Typecast;
import cetus.hir.DataFlowTools;
import cetus.hir.SymbolTools;
import cetus.hir.PrintTools;
import cetus.hir.IRTools;
import cetus.hir.TranslationUnit;
import cetus.hir.Traversable;
import cetus.hir.Program;
import cetus.hir.ExpressionStatement;
import cetus.hir.SymbolTable;
import cetus.hir.Specifier;
import cetus.hir.Identifier;
import cetus.hir.UnaryExpression;
import cetus.hir.UnaryOperator;
import cetus.hir.VariableDeclaration;
import cetus.hir.VariableDeclarator;

public abstract class AnalysisTools {

	private AnalysisTools()
	{
	}

	static final String[] not_allowed_omp_constructs1 = {
		"flush", "ordered", "barrier", "single", "master"
	};
	static final String[] not_allowed_omp_constructs2 = {
		"critical", "atomic" 
	};
	static final String[] not_allowed_omp_constructs3 = {
		"single", "master"
	};
	static List not_allowed_consts1 = Arrays.asList(not_allowed_omp_constructs1);
	static List not_allowed_consts2 = Arrays.asList(not_allowed_omp_constructs2);
	static List not_allowed_consts3 = Arrays.asList(not_allowed_omp_constructs3);
	
	static private final String[] predefinedCVars = {"stdin", "stdout",
	"stderr"};
	
	static List predefinedCVarList = new LinkedList(Arrays.asList(predefinedCVars));

	public static int checkKernelEligibility(Statement stmt) {
		int eligibility = 0;
		if( (stmt instanceof CompoundStatement) || (stmt instanceof ForLoop) ) {
			if( stmt.containsAnnotation(CudaAnnotation.class, "nogpurun") ) {
				eligibility = 6; // User prevents this statement from executing on the GPU. 
			} else {
				List<OmpAnnotation> omp_annots = IRTools.collectPragmas(stmt, OmpAnnotation.class, "for");
				DepthFirstIterator iter = new DepthFirstIterator(stmt);
				while(iter.hasNext())
				{
					Object obj = iter.next();
					if (obj instanceof Annotatable)
					{
						Annotatable at = (Annotatable)obj;
						List<OmpAnnotation> annotList = at.getAnnotations(OmpAnnotation.class);
						if( (annotList != null) && (annotList.size() > 0) ) {
							if( annotList.size() > 1 ) {
								Tools.exit("[ERROR in checkKernelEligibility()] more than one OmpAnnotations" +
								"were found!");
							}
							OmpAnnotation annot = annotList.get(0);
							if( annot != null ) {
								if( !Collections.disjoint(not_allowed_consts1, annot.keySet()) ) {
									eligibility = 2;
									break;
								} else if( !Collections.disjoint(not_allowed_consts2, annot.keySet()) ) {
									eligibility = 1;
									break;
								} else if( !Collections.disjoint(not_allowed_consts3, annot.keySet()) ) {
									eligibility = 5;
									break;
								} else if( annot.keySet().contains("parallel") ) {
									if( !stmt.equals(obj) ) {
										eligibility = 4; //nested parallel regions
										break;
									}
								}
							}
						}
					}
				}
				if( eligibility == 0 && (omp_annots.size() == 0) ) {
					eligibility = 3;
				}
			}
		} else {
			eligibility = 7;
		}
		return eligibility;
	}
	public static void addRangeDomainToCFG(DFAGraph cfg, Map<Statement, RangeDomain> range_map)
	{
		PrintTools.println("[addRangeDomainToCFG] strt", 6);

		TreeMap<Integer,DFANode> work_list = new TreeMap<Integer,DFANode>();

		Iterator<DFANode> iter = cfg.iterator();
		while ( iter.hasNext() )
		{
			DFANode node = iter.next();
			work_list.put((Integer)node.getData("top-order"), node);
		}

		for ( Integer order : work_list.keySet() )
		{
			DFANode node = work_list.get(order);

			Object ir = node.getData(Arrays.asList("super-entry","stmt"));

			RangeDomain rd = range_map.get(ir);

			if ( rd != null )
			{
				node.putData("range", rd.clone());
			}
			else if ( order == 0 )
			{
				RangeDomain range = range_map.get(node.getData("stmt"));

				if ( range == null )
					node.putData("range", new RangeDomain());
				else
					node.putData("range", range.clone());
			}
			else
			{
				RangeDomain range = null;
				int count = 0;
				for ( DFANode pred : node.getPreds() )
				{
					RangeDomain pred_range = (RangeDomain)pred.getData("range");


					if ( pred_range == null )
					{
						pred_range = new RangeDomain();
					}

					if ( range == null )
					{
						range = (RangeDomain)pred_range.clone();
					}
					else
					{
						range.unionRanges(pred_range);
					}
				}
				node.putData("range", range);
			}
		}

		PrintTools.println("[addRangeDomainToCFG] done", 6);

	}

	public static void displayCFG(CFGraph cfg, int debug_level)
	{
		if (debug_level >= 5)
		{
			System.out.println("[displayCFG] strt ----------------------");
			for ( int i=0; i<cfg.size(); i++)
			{
				DFANode node = cfg.getNode(i);
				PrintTools.println("\n" + node.toDot("tag,ir", 1), 5);
	
				Section.MAP may_def_in = (Section.MAP)node.getData("may_def_in");
				if (may_def_in != null) PrintTools.println("    may_def_in" + may_def_in, 9);
	
				Section.MAP must_def_in = (Section.MAP)node.getData("must_def_in");
				if (must_def_in != null) PrintTools.println("    must_def_in" + must_def_in, 9);
	
				Section.MAP may_def_out = (Section.MAP)node.getData("may_def_out");
				if (may_def_out != null) PrintTools.println("    may_def_out" + may_def_out, 5);
	
				Section.MAP must_def_out = (Section.MAP)node.getData("must_def_out");
				if (must_def_out != null) PrintTools.println("    must_def_out" + must_def_out, 5);
	
				Section.MAP ueuse = (Section.MAP)node.getData("ueuse");
				if (ueuse != null) PrintTools.println("    ueuse" + ueuse, 5);
	
				Section.MAP live_out = (Section.MAP)node.getData("live_out");
				if (live_out != null) PrintTools.println("    live_out" + live_out, 5);
			}
			System.out.println("[displayCFG] done ----------------------");
		}
		PrintTools.println(cfg.toDot("tag,ir,ueuse,must_def_out", 3), 5);
	}
	
	public static Statement getStatementBefore(CompoundStatement parent, Statement ref_stmt) {
		List<Traversable> children = parent.getChildren();
		int index = Tools.indexByReference(children, ref_stmt);
		if( index <= 0 ) {
			return null;
		}
		return (Statement)children.get(index-1);
	}
	
	public static Statement getStatementAfter(CompoundStatement parent, Statement ref_stmt) {
		List<Traversable> children = parent.getChildren();
		int index = Tools.indexByReference(children, ref_stmt);
		if( (index == -1) || (index == children.size()-1) ) {
			return null;
		}
		return (Statement)children.get(index+1);
	}
	
	public static Set<Symbol> getOmpSharedVariables(Traversable tr)
	{
		Set<Symbol> ret = new HashSet<Symbol>();

		List<OmpAnnotation>
		omp_annots = IRTools.collectPragmas(tr, OmpAnnotation.class, "shared");

		for (OmpAnnotation annot : omp_annots)
		{ 
			Set<Symbol> shared_set = (Set<Symbol>)annot.get("shared");
			if (shared_set == null)
				Tools.exit("[ERROR] omp shared construct has null shared set");
			else    
			{
				ret.addAll(shared_set);
			}
		}
		return ret;
	}
	
	public static Set<Symbol> getIpOmpSharedVariables(Traversable tr)
	{
		Set<Symbol> ret = new HashSet<Symbol>();
		Set<Symbol> tSet = new HashSet<Symbol>();

		List<OmpAnnotation>
		omp_annots = IRTools.collectPragmas(tr, OmpAnnotation.class, "shared");
		for (OmpAnnotation annot : omp_annots)
		{ 
			Set<Symbol> shared_set = (Set<Symbol>)annot.get("shared");
			if (shared_set == null)
				Tools.exit("[ERROR] omp shared construct has null shared set");
			else    
			{
				tSet.addAll(shared_set);
			}
		}
		for( Symbol iSym : tSet ) {
			List symInfo = AnalysisTools.findOrgSymbol(iSym, tr);
			if( symInfo.size() == 0 ) {
				ret.add(iSym);
			} else {
				ret.add((Symbol)symInfo.get(0));
			}
		}
		
		List<FunctionCall> calledFuncs = IRTools.getFunctionCalls(tr);
		for( FunctionCall fCall : calledFuncs ) {
			Procedure proc = fCall.getProcedure();
			if( proc != null ) {
				ret.addAll(getIpOmpSharedVariables(proc));
			}
		}
		return ret;
	}
	
	public static Set<Symbol> getIpAccessedVariableSymbols(Traversable t) {
		Set<Symbol> accessedSymbols = SymbolTools.getAccessedSymbols(t);
		Set<Symbol> tSet = new HashSet<Symbol>();
		for( Symbol sm : accessedSymbols ) {
			if( (sm instanceof Procedure) || (sm instanceof ProcedureDeclarator) ) {
				tSet.add(sm);
			}
		}
		accessedSymbols.removeAll(tSet);
		List<FunctionCall> calledFuncs = IRTools.getFunctionCalls(t);
		for( FunctionCall call : calledFuncs ) {
			Procedure called_procedure = call.getProcedure();
			if( called_procedure != null ) {
				CompoundStatement body = called_procedure.getBody();
				Set<Symbol> procAccessedSymbols = getIpAccessedGlobalorStaticSymbols(body);
				accessedSymbols.addAll(procAccessedSymbols);
			}
		}
		return accessedSymbols;
	}
	
	public static Set<Symbol> getIpAccessedGlobalorStaticSymbols(SymbolTable st) {
		Set<Symbol> rSet = new HashSet<Symbol>();
		Set<Symbol> aSet = SymbolTools.getAccessedSymbols(st);
		Set<Symbol> tSet = new HashSet<Symbol>();
		for( Symbol sm : aSet ) {
			if( (sm instanceof Procedure) || (sm instanceof ProcedureDeclarator) ) {
				tSet.add(sm);
			}
		}
		aSet.removeAll(tSet);
		Set<Symbol> staticSet = getStaticVariables(aSet);
		rSet.addAll(staticSet);
		aSet.removeAll(staticSet);
		Set<Symbol> localSet = SymbolTools.getLocalSymbols(st);
		aSet.removeAll(localSet);
		for( Symbol sym : aSet ) {
			if( !SymbolTools.isFormal(sym) ) {
				rSet.add(sym);
			}
		}
		List<FunctionCall> calledFuncs = IRTools.getFunctionCalls(st);
		for( FunctionCall call : calledFuncs ) {
			Procedure called_procedure = call.getProcedure();
			if( called_procedure != null ) {
				CompoundStatement body = called_procedure.getBody();
				Set<Symbol> procAccessedSymbols = getIpAccessedGlobalorStaticSymbols(body);
				rSet.addAll(procAccessedSymbols);
			}
		}
		return rSet;
	}
	
	public static Symbol getOrgSymbolOfExternOne(Symbol inSym, Program prog) {
		Symbol orgSym = null;
		if( inSym == null ) {
			return orgSym;
		}
		List specList = inSym.getTypeSpecifiers();
		if(!specList.contains(Specifier.EXTERN) ) {
			return inSym;
		}
		String extSName = inSym.getSymbolName();
		for ( Traversable tt : prog.getChildren() )
		{
			if( orgSym != null ) {
				break;
			}
			Set<Symbol> gSymbols = SymbolTools.getGlobalSymbols(tt);
			for( Symbol gSym : gSymbols ) {
				if(gSym.getSymbolName().equals(extSName)) {
					specList = gSym.getTypeSpecifiers();
					if(!specList.contains(Specifier.EXTERN) ) {
						orgSym = gSym;
						break;
					}
				}
			}
		}
		return orgSym;
	}
	
	public static List findOrgSymbol(Symbol inSym, Traversable t) {
		List symbolInfo = new LinkedList();
		Symbol tSym = null;
		Set<Symbol> symSet = null;
		Procedure p_proc = null;
		TranslationUnit t_unit = null;
		Program program = null;
		while (true) {
			if (t instanceof Procedure) break;
			t = t.getParent(); 
		}
		p_proc = (Procedure)t;
		while (true) {
			if (t instanceof TranslationUnit) break;
			t = t.getParent(); 
		}
		t_unit = (TranslationUnit)t;
		program = (Program)t_unit.getParent();
		String pName = p_proc.getSymbolName();
		if( pName.equals("main") || pName.equals("MAIN__") ) {
			tSym = getOrgSymbolOfExternOne(inSym, program);
			if( tSym == null ) {
				if( !predefinedCVarList.contains(inSym.getSymbolName())) {
					PrintTools.println("[WARNING in findOrgSymbol()] case1: can not find the original symbol" +
						" that the extern symbol (" + inSym + ") refers to; return an empty list.", 0); 
				}
				return symbolInfo;
			} else {
				symbolInfo.add(tSym);
				symbolInfo.add(p_proc);
				return symbolInfo;
			}
		}
	
		List<FunctionCall> funcCallList = IRTools.getFunctionCalls(program);
		boolean complexExp = false;
		while (true) {
			symSet = SymbolTools.getVariableSymbols((SymbolTable)p_proc);
			if( symSet.contains(inSym) ) { 
				if( (SymbolTools.isArray(inSym) || SymbolTools.isPointer(inSym)) ) {
					// Find the caller procedure that called this procedure.
					List paramList = p_proc.getParameters();
					int list_size = paramList.size();
					if( list_size == 1 ) {
						Object obj = paramList.get(0);
						String paramS = obj.toString();
						// Remove any leading or trailing whitespace.
						paramS = paramS.trim();
						if( paramS.equals(Specifier.VOID.toString()) ) {
							list_size = 0;
						}
					}
					Procedure t_proc = p_proc;
					Symbol currArgSym = null;
					Symbol prevArgSym = null;
					boolean foundArg = false;
					for( FunctionCall funcCall : funcCallList ) {
						if(t_proc.getName().equals(funcCall.getName())) {
							t = funcCall.getStatement();
							while( (t != null) && !(t instanceof Procedure) ) {
								t = t.getParent();
							}
							p_proc = (Procedure)t;
							List argList = funcCall.getArguments();
							for( int i=0; i<list_size; i++ ) {
								List declaredSyms = ((Declaration)paramList.get(i)).getDeclaredIDs();
								if( declaredSyms.contains(new Identifier(inSym)) ) {
									// Found an actual argument for the inSym. 
									foundArg = true;
									Expression exp = (Expression)argList.get(i);
									boolean acceptableArg = false;
									if( exp instanceof Literal ) {
										PrintTools.println("[INFO in findOrgSymbol()] argument (" + exp + 
												") passed for " + "the parameter symbol (" + inSym + 
												") of a procedure, " + t_proc.getName() + ", is a literal", 2);
										symbolInfo.add(inSym);
										return symbolInfo;
									} else if( exp instanceof Identifier ) {
										acceptableArg = true;
									} else if ( exp instanceof UnaryExpression ) {
										UnaryExpression uexp = (UnaryExpression)exp;
										if( uexp.getOperator().equals(UnaryOperator.ADDRESS_OF) &&
											(uexp.getExpression() instanceof Identifier) ) {
												acceptableArg = true;
											}
									} else if ( exp instanceof Typecast ) {
										Typecast texp = (Typecast)exp;
										if( (texp.getExpression() instanceof Identifier) ) {
												acceptableArg = true;
											}
									}
									if( !acceptableArg ) {
										PrintTools.println("[WARNING in findOrgSymbol()] argument (" + exp + 
												") passed for " + "the parameter symbol (" + inSym + 
												") of a procedure, " + t_proc.getName() + ", has complex expression; " +
												"this symbol may be aliased to other symbols.",1);
										complexExp = true;
									}
									Symbol extSym = SymbolTools.getSymbolOf(exp);
									currArgSym = getOrgSymbolOfExternOne(extSym, program);
									if( currArgSym == null ) {
										if( extSym == null ) {
											PrintTools.println("[WARNING in findOrgSymbol()] can not find the symbol" +
													" of the function argument (" + exp + "); return an empty list.", 0); 
										} else {
											if( !predefinedCVarList.contains(extSym.getSymbolName())) {
												PrintTools.println("[WARNING in findOrgSymbol()] case2: can not find the original symbol" +
													" that the extern symbol (" + extSym + ") refers to; return an empty list.", 0); 
											}
										}
										return symbolInfo;
									}
									if( prevArgSym == null ) {
										prevArgSym = currArgSym;
									} else if( !currArgSym.equals(prevArgSym) ) {
										// Multiple argument symbols are found.
										PrintTools.println("[WARNING in findOrgSymbol()] multiple argments exist " +
												"for the parameter symbol (" + inSym + ") of procedure (" 
												+ t_proc.getSymbolName() + "); can't find the original symbol", 1);
										return symbolInfo;
									}
									break;
								}
							}
						}
					}
					if( foundArg ) {
						inSym = currArgSym;
					} else {
						String tpName = t_proc.getSymbolName();
						if( tpName.equals("main") || tpName.equals("MAIN__") ) {
							symbolInfo.add(inSym);
							return symbolInfo;
						} else {
							PrintTools.println("[WARNING in findOrgSymbol()] can not find the argument passed for " +
									"the parameter symbol (" + inSym + ") of a procedure, " + t_proc.getName() + ".", 0);
							return symbolInfo;
						}
					}
				} else if( SymbolTools.isScalar(inSym) ) {
					symbolInfo.add(inSym);
					return symbolInfo;
				} else {
					PrintTools.println("[WARNING in findOrgSymbol()] Unknown type found", 0);
					return symbolInfo;
				}
			} else {
				break;
			}
		}
		tSym = getOrgSymbolOfExternOne(inSym, program);
		if( tSym == null ) {
			if( !predefinedCVarList.contains(inSym.getSymbolName())) {
				PrintTools.println("[WARNING in findOrgSymbol()] case3: can not find the original symbol" +
						" that the extern symbol (" + inSym + ") refers to; return an empty list.", 0); 
			}
			return symbolInfo;
		}
		inSym = tSym;
		if( complexExp ) {
			symbolInfo.add(inSym);
			return symbolInfo;
		}
		if( SymbolTools.isGlobal(inSym) ) {
			symbolInfo.add(inSym);
			symbolInfo.add((TranslationUnit)p_proc.getParent());
			return symbolInfo;
		}
		symSet = SymbolTools.getLocalSymbols((SymbolTable)p_proc.getBody());
		if( symSet.contains(inSym) ) {
			String name = p_proc.getSymbolName();
			List<Specifier> specs = inSym.getTypeSpecifiers();
			symbolInfo.add(inSym);
			if( specs.contains(Specifier.STATIC) 
					|| name.equals("main") || name.equals("MAIN__") ) {
				symbolInfo.add(p_proc);
			}
			return symbolInfo;
		}
		PrintTools.println("[WARNING in findOrgSymbol()] Can't find the original symbol; return  an empty list", 0);
		return symbolInfo;
	}
	
	public static Traversable findEnclosingParallelRegion(Traversable t) {
		OmpAnnotation pAnnot = null;
		while( !(t instanceof Annotatable) ) {
			t = t.getParent();
		}
		pAnnot = ((Annotatable)t).getAnnotation(OmpAnnotation.class, "parallel");
		while( (pAnnot == null) && !(t instanceof Procedure) ) {
			t = t.getParent();
			pAnnot = ((Annotatable)t).getAnnotation(OmpAnnotation.class, "parallel");
		}
		if( pAnnot != null ) {
			return t;
		}
		if( t instanceof Procedure ) {
			Procedure t_proc = (Procedure)t;
			while( !(t instanceof Program) ) {
				t = t.getParent();
			}
			List<FunctionCall> funcCallList = IRTools.getFunctionCalls(t);
			for( FunctionCall funcCall : funcCallList ) {
				if(t_proc.getName().equals(funcCall.getName())) {
					t = findEnclosingParallelRegion(funcCall.getStatement());
					if( t != null ) {
						return t;
					}
				}
			}
		}
		return null;
	}
	
	public static boolean checkSharedVariableAccess( Symbol sharedVar, Traversable tr ) {
		boolean isAccessed = false;
		isAccessed = IRTools.containsSymbol(tr, sharedVar);
		if( !isAccessed ) {
			Expression expr = null;
			if( tr instanceof ExpressionStatement ) {
				expr = ((ExpressionStatement)tr).getExpression();
			} else if( tr instanceof Expression ) {
				expr = (Expression)tr;
			}
			if( (expr != null) && (expr instanceof FunctionCall) ) {
				isAccessed = IRTools.containsSymbol(((FunctionCall)expr).getProcedure(), sharedVar);
			}
		}
		return isAccessed;
	}
	
	public static boolean isClassMember(VariableDeclarator varSym) {
		Traversable t = varSym.getParent();
		boolean foundParentClass = false;
		while( t != null ) {
			if( t instanceof ClassDeclaration ) {
				foundParentClass = true;
				break;
			} else {
				t = t.getParent();
			}
		}
		return foundParentClass;
	}
	
	  public static <T extends PragmaAnnotation> List<T>
	      ipCollectPragmas(Traversable t, Class<T> pragma_cls, String key)
	  {
	    List<T> ret = new LinkedList<T>();

	    DepthFirstIterator iter = new DepthFirstIterator(t);
	    while ( iter.hasNext() )
	    {
	      Object o = iter.next();
	      if ( o instanceof Annotatable )
	      {
	        Annotatable at = (Annotatable)o;
	        List<T> pragmas = at.getAnnotations(pragma_cls);
	        if( pragmas != null ) {
	          for ( T pragma : pragmas )
	            if ( pragma.containsKey(key) )
	              ret.add(pragma);
	        }
	      } else if( o instanceof FunctionCall ) {
	    	  FunctionCall funCall = (FunctionCall)o;
	    	  if( !StandardLibrary.contains(funCall) ) {
	    		  Procedure calledProc = funCall.getProcedure();
	    		  if( calledProc != null ) { 
	    			  ret.addAll(ipCollectPragmas(calledProc, pragma_cls, key));
	    		  }
	    	  }
	      }
	    }
	    return ret;
	  }
	
	public static void markIntervalForKernelRegions(Program program) {
		DepthFirstIterator proc_iter = new DepthFirstIterator(program);
		Set<Procedure> proc_list = (Set<Procedure>)(proc_iter.getSet(Procedure.class));
		CompoundStatement target_parent;
		for (Procedure proc : proc_list)
		{
			List<OmpAnnotation>
			omp_annots = IRTools.collectPragmas(proc, OmpAnnotation.class, "parallel");
			for ( OmpAnnotation annot : omp_annots )
			{
				Statement target_stmt = (Statement)annot.getAnnotatable();
				int eligibility = AnalysisTools.checkKernelEligibility(target_stmt);
				if( eligibility == 0 ) {
					target_parent = (CompoundStatement)target_stmt.getParent();
					target_parent.addStatementBefore(target_stmt, SplitOmpPRegion.insertBarrier("S2P"));
					target_parent.addStatementAfter(target_stmt, SplitOmpPRegion.insertBarrier("P2S"));
				} else if (eligibility == 3) {
					if( annot.containsKey("for") ) {
						eligibility = 0;
					} else {
						List<FunctionCall> funcCalls = IRTools.getFunctionCalls(target_stmt); 
						for( FunctionCall calledProc : funcCalls ) {
							Procedure tProc = calledProc.getProcedure();
							if( tProc != null ) {
								eligibility = AnalysisTools.checkKernelEligibility(tProc.getBody());
								if(  eligibility == 0 ) {
									break;
								}
							}
						}
					}
					if( eligibility == 0 ) {
						target_parent = (CompoundStatement)target_stmt.getParent();
						target_parent.addStatementBefore(target_stmt, SplitOmpPRegion.insertBarrier("S2P"));
						target_parent.addStatementAfter(target_stmt, SplitOmpPRegion.insertBarrier("P2S"));
					}
				} 
			}
		}
	}
	
	public static class REGIONMAP extends HashMap<Symbol,String> implements Cloneable
	{
		private static final long serialVersionUID = 14L;	
		public REGIONMAP()
		{
			super();
		}

		public REGIONMAP(Symbol var, String region)
		{
			super();
			put(var, region);
		}

		public Object clone()
		{
			REGIONMAP o = new REGIONMAP();

			for ( Symbol var : keySet() )
				o.put(var, get(var));

			return o;
		}
		public boolean retainAll(REGIONMAP other, String diffStr)
		{
			boolean changed = false;
			if ( other == null && !isEmpty() ) {
				changed = true;
				clear();
			}
			for ( Symbol var : keySet() )
			{
				String s1 = get(var);
				String s2 = other.get(var);

				if ( s2 == null ) {
					changed = true;
					remove(var);
				} else if( !s1.equals(s2) ) {
					changed = true;
					//put(var, new String(diffStr));
					if( diffStr.equals("multiple") ) {
						if( s1.equals("CPU") && s2.equals("GPU") ) {
							put(var, new String("CPUGPU"));
						} else if( s1.equals("GPU") && s2.equals("CPU") ) {
							put(var, new String("GPUCPU"));
						} else {
							put(var, new String("Unknown"));
						}
							
					} else {
						put(var, new String(diffStr));
					}
				}
			}
			return changed;
		}
		
		static public boolean retainAllS(HashMap<String, String> orgMap, HashMap<String, String> otherMap, String diffStr)
		{
			boolean changed = false;
			if ( otherMap == null && !orgMap.isEmpty() ) {
				changed = true;
				orgMap.clear();
			}
			for ( String var : orgMap.keySet() )
			{
				String s1 = orgMap.get(var);
				String s2 = otherMap.get(var);

				if ( s2 == null ) {
					changed = true;
					orgMap.remove(var);
				} else if( !s1.equals(s2) ) {
					changed = true;
					if( diffStr.equals("multiple") ) {
						if( s1.equals("CPU") && s2.equals("GPU") ) {
							orgMap.put(var, new String("CPUGPU"));
						} else if( s1.equals("GPU") && s2.equals("CPU") ) {
							orgMap.put(var, new String("GPUCPU"));
						} else {
							orgMap.put(var, new String("Unknown"));
						}
							
					} else {
						orgMap.put(var, new String(diffStr));
					}
				}
			}
			return changed;
		}

		public REGIONMAP intersectWith(REGIONMAP other, String diffStr)
		{
			REGIONMAP ret = new REGIONMAP();

			if ( other == null )
				return ret;

			for ( Symbol var : keySet() )
			{
				String s1 = get(var);
				String s2 = other.get(var);

				if ( s1 == null || s2 == null )
					continue;

				if( s1.equals(s2) ) {
					ret.put(var, s1);
				} else {
					if( diffStr.equals("multiple") ) {
						if( s1.equals("CPU") && s2.equals("GPU") ) {
							ret.put(var, new String("CPUGPU"));
						} else if( s1.equals("GPU") && s2.equals("CPU") ) {
							ret.put(var, new String("GPUCPU"));
						} else {
							ret.put(var, new String("Unknown"));
						}
							
					} else {
						ret.put(var, new String(diffStr));
					}
				}
			}
			return ret;
		}
		
		/**
		 * add other region map to this region map.
		 *
		 * @param other the other region map to be added.
		 * @param diffStr string that will be inserted when two REGIONMAPs have different values.
		 * @return true if anything is changed or added.
		 */
		public boolean addAll(REGIONMAP other, String diffStr)
		{
			boolean changed = false;
			if ( other == null )
				return changed;

			for ( Symbol var : other.keySet() )
			{
				String s1 = get(var);
				String s2 = other.get(var);

				if ( s1 == null && s2 == null )
					continue;

				if ( s1 == null )
				{
					changed = true;
					put(var, s2);
				}
				else if ( s2 != null )
				{
					if( !s1.equals(s2) ) {
						changed = true;
						//put(var, new String(diffStr));
						if( diffStr.equals("multiple") ) {
							if( s1.equals("CPU") && s2.equals("GPU") ) {
								put(var, new String("CPUGPU"));
							} else if( s1.equals("GPU") && s2.equals("CPU") ) {
								put(var, new String("GPUCPU"));
							} else {
								put(var, new String("Unknown"));
							}
								
						} else {
							put(var, new String(diffStr));
						}
					}
				}
			}
			return changed;
		}
		

		static public boolean addAllS(HashMap<String,String> orgMap, HashMap<String, String> otherMap, String diffStr)
		{
			boolean changed = false;
			if ( otherMap == null )
				return changed;

			for ( String var : otherMap.keySet() )
			{
				String s1 = orgMap.get(var);
				String s2 = otherMap.get(var);

				if ( s1 == null && s2 == null )
					continue;

				if ( s1 == null )
				{
					changed = true;
					orgMap.put(var, s2);
				}
				else if ( s2 != null )
				{
					if( !s1.equals(s2) ) {
						changed = true;
						//orgMap.put(var, new String(diffStr));
						if( diffStr.equals("multiple") ) {
							if( s1.equals("CPU") && s2.equals("GPU") ) {
								orgMap.put(var, new String("CPUGPU"));
							} else if( s1.equals("GPU") && s2.equals("CPU") ) {
								orgMap.put(var, new String("GPUCPU"));
							} else {
								orgMap.put(var, new String("Unknown"));
							}
								
						} else {
							orgMap.put(var, new String(diffStr));
						}
					}
				}
			}
			return changed;
		}


		public REGIONMAP unionWith(REGIONMAP other, String diffStr)
		{
			if ( other == null )
				return (REGIONMAP)clone();

			REGIONMAP ret = new REGIONMAP();

			Set<Symbol> vars = new HashSet<Symbol>(keySet());
			vars.addAll(other.keySet());

			for ( Symbol var : vars )
			{
				String s1 = get(var);
				String s2 = other.get(var);

				if ( s1 == null && s2 == null )
					continue;

				if ( s1 == null )
				{
					ret.put(var, s2);
				}
				else if ( s2 == null )
					ret.put(var, s1);
				else
				{
					if( s1.equals(s2) ) {
						ret.put(var, s1);
					} else {
						if( diffStr.equals("multiple") ) {
							if( s1.equals("CPU") && s2.equals("GPU") ) {
								ret.put(var, new String("CPUGPU"));
							} else if( s1.equals("GPU") && s2.equals("CPU") ) {
								ret.put(var, new String("GPUCPU"));
							} else {
								ret.put(var, new String("Unknown"));
							}
								
						} else {
							ret.put(var, new String(diffStr));
						}
					}
				}
			}
			return ret;
		}
		

		public REGIONMAP overwritingUnionWith(REGIONMAP other)
		{
			if ( other == null )
				return (REGIONMAP)clone();

			REGIONMAP ret = new REGIONMAP();

			Set<Symbol> vars = new HashSet<Symbol>(keySet());
			vars.addAll(other.keySet());

			for ( Symbol var : vars )
			{
				String s1 = get(var);
				String s2 = other.get(var);

				if ( s1 == null && s2 == null )
					continue;

				if ( s1 == null ) {
					ret.put(var, s2);
				} else {
					ret.put(var, s1);
				}
			}
			return ret;
		}
		

		public void removeSideAffected(Traversable tr)
		{
			DepthFirstIterator iter = new DepthFirstIterator(tr);

			iter.pruneOn(FunctionCall.class);

			while ( iter.hasNext() )
			{
				Object o = iter.next();
				if ( o instanceof FunctionCall )
				{
					Set<Symbol> vars = new HashSet<Symbol>(keySet());
					FunctionCall fc = (FunctionCall)o;
					if( !StandardLibrary.contains(fc) ) {
						for ( Symbol var : vars ) {
							Set<Symbol> params = SymbolTools.getAccessedSymbols(fc);
							// Case 1: variables are used as parameters.
							if ( params.contains(var) && (SymbolTools.isArray(var) || SymbolTools.isPointer(var)) ) {
								put(var, new String("Unknown"));
							}
							// Case 2: variables are global.
							if ( SymbolTools.isGlobal(var, fc) ) {
								put(var, new String("Unknown"));
							}
						}
					}
				}
			}
		}
		

		public void updateSymbols(Traversable t) {
			HashSet<Symbol> old_set = new HashSet<Symbol>(keySet());
			HashSet<Symbol> new_set = new HashSet<Symbol>();
			AnalysisTools.updateSymbols(t, old_set, new_set, false);
			for( Symbol oSym : old_set ) {
				String old_sym = oSym.getSymbolName();
				String region = get(oSym);
				remove(oSym);
				for( Symbol nSym : new_set ) {
					if( nSym.getSymbolName().equals(old_sym) ) {
						put(nSym, region);
						break;
					}
				}
			}
		}
	}
	

	  public static Section.MAP getUseSectionMap(Expression e, RangeDomain rd, Set<Symbol> def_vars)
	  {
	    Section.MAP ret = new Section.MAP();

	    Expression expr = rd.substituteForward(e);

	    if ( expr instanceof ArrayAccess )
	    {
	      ArrayAccess aa = (ArrayAccess)expr;

	      Symbol var = SymbolTools.getSymbolOf(aa.getArrayName());
	      if( var instanceof AccessSymbol ) {
	    	  var = ((AccessSymbol)var).getIRSymbol();
	      }

	      Section new_section = new Section(aa);
	      new_section.expandMay(rd, def_vars);
	      ret.put(var, new_section);
	    }
	    else if ( expr instanceof AccessExpression )
	    {
	      Set use_set = DataFlowTools.getUseSet(expr);
	      if ( use_set.size() == 1 )
	      {

	        Symbol var = SymbolTools.getSymbolOf(expr);
	        if (var instanceof PseudoSymbol)
	          var = ((PseudoSymbol)var).getIRSymbol();
	        ret.put(var, new Section(-1));
	      }
	    }
	    else
	    {
	      Symbol var = SymbolTools.getSymbolOf(expr);
	      if( var instanceof AccessSymbol ) {
	    	  var = ((AccessSymbol)var).getIRSymbol();
	      }

	      if ( var != null ) {
	        ret.put(var, new Section(-1));
	      } else {

	        if ( e instanceof ArrayAccess )
	        {
	          ArrayAccess aa = (ArrayAccess)e;

	          Symbol var2 = SymbolTools.getSymbolOf(aa.getArrayName());
	          if( var2 instanceof AccessSymbol ) {
	        	  var2 = ((AccessSymbol)var2).getIRSymbol();
	          }

	          Section new_section = new Section(aa);
	          new_section.expandMay(rd, def_vars);
	          ret.put(var2, new_section);
	        }
	        else if ( e instanceof AccessExpression )
	        {
	          Set use_set = DataFlowTools.getUseSet(e);
	          if ( use_set.size() == 1 )

	            Symbol var2 = SymbolTools.getSymbolOf(e);
	            if (var2 instanceof PseudoSymbol)
	              var2 = ((PseudoSymbol)var2).getIRSymbol();
	            ret.put(var2, new Section(-1));
	          }
	        }
	        else
	        {
	          Symbol var2 = SymbolTools.getSymbolOf(e);
	          if( var2 instanceof AccessSymbol ) {
	        	  var2 = ((AccessSymbol)var2).getIRSymbol();
	          }

	          if ( var2 != null ) {
	            ret.put(var2, new Section(-1));
	          }
	        }
	        
	      }
	    }

	    ret.clean();

	    return ret;
	  }


	  public static Section.MAP getDefSectionMap(Expression e, RangeDomain rd, Set<Symbol> def_vars)
	  {
	    Section.MAP ret = new Section.MAP();

	    Expression expr = rd.substituteForward(e);

	    if ( expr instanceof ArrayAccess )
	    {
	      ArrayAccess aa = (ArrayAccess)expr;

	      Symbol var = SymbolTools.getSymbolOf(aa.getArrayName());
	      if( var instanceof AccessSymbol ) {
	    	  var = ((AccessSymbol)var).getIRSymbol();
	      }

	      Section new_section = new Section(aa);
	      new_section.expandMay(rd, def_vars);
	      ret.put(var, new_section);
	    }
	    else
	    {
	      Symbol var = SymbolTools.getSymbolOf(expr);
	      if( var instanceof AccessSymbol ) {
	    	  var = ((AccessSymbol)var).getIRSymbol();
	      }

	      if ( var != null ) {
	        ret.put(var, new Section(-1));
	       }else {

	        if ( e instanceof ArrayAccess )
	        {
	          ArrayAccess aa = (ArrayAccess)e;

	          Symbol var2 = SymbolTools.getSymbolOf(aa.getArrayName());
	          if( var2 instanceof AccessSymbol ) {
	        	  var2 = ((AccessSymbol)var2).getIRSymbol();
	          }

	          Section new_section = new Section(aa);
	          new_section.expandMay(rd, def_vars);
	          ret.put(var2, new_section);
	        }
	        else
	        {
	          Symbol var2 = SymbolTools.getSymbolOf(e);
	          if( var2 instanceof AccessSymbol ) {
	        	  var2 = ((AccessSymbol)var2).getIRSymbol();
	          }

	          if ( var2 != null ) {
	            ret.put(var2, new Section(-1));
	          } 
	        }

	      }
	    }

	    ret.clean();

	    return ret;
	  }



	public static void annotateBarriers(Procedure proc, CFGraph cfg) {
		HashSet<Statement> s2pBarriers = new HashSet<Statement>();
		HashSet<Statement> p2sBarriers = new HashSet<Statement>();
		HashMap<Statement, Statement> s2pRegions = new HashMap<Statement, Statement>();
		HashMap<Statement, Statement> p2sRegions = new HashMap<Statement, Statement>();
		List<OmpAnnotation> bBarrier_annots = (List<OmpAnnotation>)
		IRTools.collectPragmas(proc.getBody(), OmpAnnotation.class, "barrier");
		for( OmpAnnotation omp_annot : bBarrier_annots ) {
			String type = (String)omp_annot.get("barrier");
			Statement bstmt = null;
			Statement pstmt = null;
			if( type.equals("S2P") ) {
				bstmt = (Statement)omp_annot.getAnnotatable();
				pstmt = AnalysisTools.getStatementAfter((CompoundStatement)bstmt.getParent(), 
						bstmt);
				s2pBarriers.add(bstmt);
				s2pRegions.put(bstmt, pstmt);
			} else if( type.equals("P2S") ) {
				bstmt = (Statement)omp_annot.getAnnotatable();
				pstmt = AnalysisTools.getStatementBefore((CompoundStatement)bstmt.getParent(), 
						bstmt);
				p2sBarriers.add(bstmt);
				p2sRegions.put(bstmt, pstmt);
			} else {
				continue;
			}
		}
		Iterator<DFANode> iter = cfg.iterator();
		while ( iter.hasNext() )
		{
			DFANode node = iter.next();
			Statement IRStmt = null;
			Object obj = node.getData("tag");
			if( obj instanceof String ) {
				String tag = (String)obj;
				if( !tag.equals("barrier") ) {
					continue;
				}
			} else {
				continue;
			}
			obj = node.getData("stmt");
			if( obj instanceof Statement ) {
				IRStmt = (Statement)obj;
			} else {
				continue;
			}

			boolean found_bBarrier = false;
			Statement foundStmt = null;
			String type = node.getData("type");
			if( type == null ) {
				Tools.exit("[ERROR in AnalysisTools.annotBarriers()] " +
						"DFANode for a barrier does not have type information!");
			} else if( type.equals("S2P") ) {
				for( Statement stmt : s2pBarriers ) {
					if( stmt.equals(IRStmt) ) {
						found_bBarrier = true;
						foundStmt = stmt;
						break;
					}
				}
				if( found_bBarrier ) {
					Statement pStmt = s2pRegions.get(foundStmt);
					node.putData("kernelRegion", pStmt);
				}
			} else if( type.equals("P2S") ) {
				for( Statement stmt : p2sBarriers ) {
					if( stmt.equals(IRStmt) ) {
						found_bBarrier = true;
						foundStmt = stmt;
						break;
					}
				}
				if( found_bBarrier ) {
					Statement pStmt = p2sRegions.get(foundStmt);
					node.putData("pKernelRegion", pStmt);
				}
			}
		}	
	}
	

	public static void liveGVariableAnalysis(CFGraph cfg, boolean includeBackEdge) {
		PrintTools.println("Run liveGVariableAnalysis", 2);
		//Check whether shrdSclrCachingOnSM is on or not.
		boolean	shrdSclrCachingOnSM = false;
		boolean	shrdSclrCachingOnConst = false;
		String value = Driver.getOptionValue("shrdSclrCachingOnSM");
		if( value != null ) {
			shrdSclrCachingOnSM = true;
		}
		value = Driver.getOptionValue("shrdSclrCachingOnConst");
		if( value == null ) {
			shrdSclrCachingOnConst = false;
		} else {
			shrdSclrCachingOnConst = true;
		}
		TreeMap work_list = new TreeMap();


		List<DFANode> exit_nodes = cfg.getExitNodes();
		if (exit_nodes.size() > 1)
		{
			PrintTools.println("[liveGVariableAnalysis] Warning: multiple exits in the program", 2);
		}

		for ( DFANode exit_node : exit_nodes )
			work_list.put((Integer)exit_node.getData("top-order"), exit_node);

		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.lastKey());
			Set<Symbol> curr_set = new HashSet<Symbol>();

			for ( DFANode succ : node.getSuccs() )
			{
				Set<Symbol> succ_set = (Set<Symbol>)succ.getData("liveG_in");
				if( succ_set != null ) {
					curr_set.addAll(succ_set);
				}
			}

			Set<Symbol> prev_set = (Set<Symbol>)node.getData("liveG_out");

			if ( prev_set == null || !prev_set.equals(curr_set) )
			{
				node.putData("liveG_out", curr_set);

				Statement stmt = node.getData("kernelRegion");
				Set<Symbol> liveG_in = new HashSet<Symbol>();
				liveG_in.addAll(curr_set);
				if( stmt != null ) {
					OmpAnnotation annot = stmt.getAnnotation(OmpAnnotation.class, "parallel");
					if( (annot != null) && (AnalysisTools.checkKernelEligibility(stmt) == 0) ) {
						Procedure proc = IRTools.getParentProcedure(stmt);
						CudaAnnotation cannot = stmt.getAnnotation(CudaAnnotation.class, "sharedRO");
						Set<String> sharedROSet = new HashSet<String>();
						if( cannot != null ) {
							sharedROSet.addAll((HashSet<String>)cannot.get("sharedRO"));
						}
						Set<Symbol> sharedVars = (Set<Symbol>)annot.get("shared");
						if( sharedVars != null ) {
							Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(stmt);
							Set<Symbol> defSyms = getBaseSymbols(tDefSyms);
							for(Symbol sSym: sharedVars) {
								boolean isStruct = false;
							if( proc.containsSymbol(sSym) ) {
									isStruct = SymbolTools.isStruct(sSym, proc);
								} else {
									isStruct = SymbolTools.isStruct(sSym, (Traversable)sSym);
								}
								if( SymbolTools.isScalar(sSym) && !defSyms.contains(sSym) &&
										shrdSclrCachingOnSM ) {
									if( isStruct ) {
										if( !shrdSclrCachingOnConst ) {
											continue;
										}
									} else {
										continue;
									}
								}
								if( sharedROSet.contains(sSym.getSymbolName()) ) {
									continue;
								}
								liveG_in.add(sSym);
							}
						}
					}
				}
			if( liveG_in.size() > 0 ) {
					Traversable ir = node.getData("ir");
					if( (ir != null) && (ir instanceof ExpressionStatement) ) {
						Expression expr = ((ExpressionStatement)ir).getExpression();
						if( expr instanceof FunctionCall ) {
							Set<Symbol> removeSet = new HashSet<Symbol>();
							for( Symbol sym: liveG_in ) {
								if( checkSharedVariableAccess(sym, expr) ) {
									removeSet.add(sym);
								}
							}
							liveG_in.removeAll(removeSet);
						}
					}
				}
				node.putData("liveG_in", liveG_in);

				DFANode temp = (DFANode)node.getData("back-edge-from");
				if( temp == null || includeBackEdge) {
					for ( DFANode pred : node.getPreds() ) {
						work_list.put(pred.getData("top-order"), pred);
					}
				} else {
					for ( DFANode pred : node.getPreds() ) {
						if( temp != pred ) {
							work_list.put(pred.getData("top-order"), pred);
						}
					}
				}
			}
		}
	}
	

	public static void advLiveGVariableAnalysis(CFGraph cfg, boolean includeBackEdge) {
		PrintTools.println("Run advLiveGVariableAnalysis", 2);
		TreeMap work_list = new TreeMap();

		List<DFANode> exit_nodes = cfg.getExitNodes();
		if (exit_nodes.size() > 1)
		{
			PrintTools.println("[advLiveGVariableAnalysis] Warning: multiple exits in the program", 2);
		}

		for ( DFANode exit_node : exit_nodes )
			work_list.put((Integer)exit_node.getData("top-order"), exit_node);

		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.lastKey());
			Set<Symbol> curr_set = new HashSet<Symbol>();

			for ( DFANode succ : node.getSuccs() )
			{
				Set<Symbol> succ_set = (Set<Symbol>)succ.getData("advLiveG_in");
				if( succ_set != null ) {
					curr_set.addAll(succ_set);
				}
			}

			Set<Symbol> prev_set = (Set<Symbol>)node.getData("advLiveG_out");

			if ( prev_set == null || !prev_set.equals(curr_set) )
			{
				node.putData("advLiveG_out", curr_set);

				Set<Symbol> advLiveG_in = new HashSet<Symbol>();
				advLiveG_in.addAll(curr_set);
				String tag = node.getData("tag");
				String type = node.getData("type");
				if( (tag != null) && (type != null) && (tag.equals("barrier")
						&& (type.equals("S2P"))) ) {
					Set<Symbol> liveG_in = node.getData("liveG_in");
					if( liveG_in == null ) {
						Tools.exit("[Error in advLiveGVariableAnalsys()] liveG_in set does not exist; " +
						"Run liveGVariableAnalysis() before this analysis.");
					}	
					advLiveG_in.addAll(liveG_in);
					Set<Symbol> reachingGMalloc_in = node.getData("reachingGMalloc_in");
					Set<Symbol> removeSet = new HashSet<Symbol>();
					if( reachingGMalloc_in == null ) {
						Tools.exit("[Error in advLiveGVariableAnalsys()] reachingGMalloc_in set does not exist; " +
						"Run reachingGMallocAnalysis() before this analysis.");
					}
					if( advLiveG_in.size() > 0 ) {
						for( Symbol sym: advLiveG_in ) {
							if( !reachingGMalloc_in.contains(sym) ) {
								removeSet.add(sym);
							}
						}
						advLiveG_in.removeAll(removeSet);
					}
				}
				
				if( advLiveG_in.size() > 0 ) {
					Traversable ir = node.getData("ir");
					if( (ir != null) && (ir instanceof ExpressionStatement) ) {
						Expression expr = ((ExpressionStatement)ir).getExpression();
						if( expr instanceof FunctionCall ) {
							Set<Symbol> removeSet = new HashSet<Symbol>();
							for( Symbol sym: advLiveG_in ) {
								if( checkSharedVariableAccess(sym, expr) ) {
									removeSet.add(sym);
								}
							}
							advLiveG_in.removeAll(removeSet);
						}
					}
				}
				node.putData("advLiveG_in", advLiveG_in);

				DFANode temp = (DFANode)node.getData("back-edge-from");
				if( temp == null || includeBackEdge) {
					for ( DFANode pred : node.getPreds() ) {
						work_list.put(pred.getData("top-order"), pred);
					}
				} else {
					for ( DFANode pred : node.getPreds() ) {
						if( temp != pred ) {
							work_list.put(pred.getData("top-order"), pred);
						}
					}
				}
			}
		}
	}

	
	public static void reachingGMallocAnalysis(CFGraph cfg) {
		//Check whether shrdSclrCachingOnSM is on or not.
		boolean	shrdSclrCachingOnSM = false;
		boolean	shrdSclrCachingOnConst = false;
		String value = Driver.getOptionValue("shrdSclrCachingOnSM");
		if( value != null ) {
			shrdSclrCachingOnSM = true;
		}
		value = Driver.getOptionValue("shrdSclrCachingOnConst");
		if( value == null ) {
			shrdSclrCachingOnConst = false;
		} else {
			shrdSclrCachingOnConst = true;
		}
		
		TreeMap work_list = new TreeMap();
	
		DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
		entry.putData("reachingGMalloc_in", new HashSet<Symbol>());
		work_list.put(entry.getData("top-order"), entry);
		
		String currentRegion = new String("CPU");
	
		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.firstKey());
			
			String tag = (String)node.getData("tag");
			if( tag != null && tag.equals("barrier") ) {
				String type = (String)node.getData("type");
				if( type != null ) {
					if( type.equals("S2P") ) {
						currentRegion = new String("GPU");
					} else if( type.equals("P2S") ) {
						currentRegion = new String("CPU");
					}
				}
			}
	
			HashSet<Symbol> GMalloc_in = null;

			for ( DFANode pred : node.getPreds() )
			{
				Set<Symbol> pred_GMalloc_out = (Set<Symbol>)pred.getData("reachingGMalloc_out");

				if ( GMalloc_in == null ) {
					if ( pred_GMalloc_out != null ) {
						GMalloc_in = new HashSet<Symbol>();
						GMalloc_in.addAll(pred_GMalloc_out);
					}
				} else {
					if ( pred_GMalloc_out != null ) {
						GMalloc_in.retainAll(pred_GMalloc_out);
					} 
				}
			}
	
			Set<Symbol> p_GMalloc_in = (Set<Symbol>)node.getData("reachingGMalloc_in");
	
			if ( (GMalloc_in == null) || (p_GMalloc_in == null) || !GMalloc_in.equals(p_GMalloc_in) ) {
				node.putData("reachingGMalloc_in", GMalloc_in);
	
				Set<Symbol> GMalloc_out = new HashSet<Symbol>();
				if( GMalloc_in != null ) {
					GMalloc_out.addAll(GMalloc_in);
				}
			Statement stmt = node.getData("kernelRegion");
				if( stmt != null ) {
					Set<Symbol> liveG_out = (Set<Symbol>)node.getData("liveG_out");
					if( liveG_out == null ) {
						Tools.exit("[Error in reachingGMallocAnalysis()] liveG_out is null; " +
								"run liveGVariableAnalysis before this analysis");
					}
					OmpAnnotation annot = stmt.getAnnotation(OmpAnnotation.class, "parallel");
					if( annot != null ) {
						Procedure proc = IRTools.getParentProcedure(stmt);
						CudaAnnotation cannot = stmt.getAnnotation(CudaAnnotation.class, "sharedRO");
						Set<String> sharedROSet = new HashSet<String>();
						if( cannot != null ) {
							sharedROSet.addAll((HashSet<String>)cannot.get("sharedRO"));
						}
						Set<String> constantSet = new HashSet<String>();
						cannot = stmt.getAnnotation(CudaAnnotation.class, "constant");
						if( cannot != null ) {
							constantSet.addAll((HashSet<String>)cannot.get("constant"));
						}
						Set<Symbol> sharedVars = (Set<Symbol>)annot.get("shared");
						Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(stmt);
						Set<Symbol> defSyms = getBaseSymbols(tDefSyms);
						if( sharedVars != null ) {
							for(Symbol sSym: sharedVars) {
								boolean isStruct = false;
							if( proc.containsSymbol(sSym) ) {
									isStruct = SymbolTools.isStruct(sSym, proc);
								} else {
									isStruct = SymbolTools.isStruct(sSym, (Traversable)sSym);
								}
								if( SymbolTools.isScalar(sSym) && !defSyms.contains(sSym) &&
										shrdSclrCachingOnSM ) {
									if( isStruct ) {
										if( !shrdSclrCachingOnConst ) {
											continue;
										}
									} else {
										continue;
									}
								}
								if( sharedROSet.contains(sSym.getSymbolName()) ) {
									continue;
								}
								if( constantSet.contains(sSym.getSymbolName()) ) {
									continue;
								}
								if( liveG_out.contains(sSym) ) {
									GMalloc_out.add(sSym);
								}
							}
						}
					} else {
						Tools.exit("[Error1 in reachingGMallocAnalysis] Incorrect tag in a node: " + node);
					}
				}
					if( GMalloc_out.size() > 0 && currentRegion.equals("CPU") ) {
					Traversable ir = node.getData("ir");
					if( (ir != null) && (ir instanceof ExpressionStatement) ) {
						Expression expr = ((ExpressionStatement)ir).getExpression();
						if( expr instanceof FunctionCall ) {
							Set<Symbol> removeSet = new HashSet<Symbol>();
							for( Symbol sym: GMalloc_out ) {
								if( checkSharedVariableAccess(sym, expr) ) {
									removeSet.add(sym);
								}
							}
							GMalloc_out.removeAll(removeSet);
						}
					}
				}
					
				node.putData("reachingGMalloc_out", GMalloc_out);
	
				for ( DFANode succ : node.getSuccs() ) {
					work_list.put(succ.getData("top-order"), succ);
				}
			}
		}
	}
	
	
	public static void cudaMallocFreeAnalsys(CFGraph cfg) {
		boolean	shrdSclrCachingOnSM = false;
		String value = Driver.getOptionValue("shrdSclrCachingOnSM");
		if( value != null ) {
			shrdSclrCachingOnSM = true;
		}
		TreeMap work_list = new TreeMap();
		HashSet<DFANode> visitedNodes = new HashSet<DFANode>();
		
		DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
		work_list.put(entry.getData("top-order"), entry);
		
		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.firstKey());

			for ( DFANode succ : node.getSuccs() ) {
				if( !visitedNodes.contains(succ) ) {
					visitedNodes.add(succ);
					work_list.put(succ.getData("top-order"), succ);
				}
			}

			Statement stmt = node.getData("kernelRegion");
			Statement pStmt = null;
			if( stmt != null ) { 
				pStmt = stmt;
			} else {
				stmt = node.getData("pKernelRegion");
				if( stmt != null ) { 
					pStmt = stmt;
				}
			}
			if( pStmt != null ) {
				OmpAnnotation annot = pStmt.getAnnotation(OmpAnnotation.class, "parallel");
				if( annot != null ) {
					Set<Symbol> cudaMallocSet = new HashSet<Symbol>();
					Set<Symbol> cudaFreeSet = new HashSet<Symbol>();
					Set<Symbol> GMalloc_in = (Set<Symbol>)node.getData("reachingGMalloc_in");
					Set<Symbol> liveG_out = (Set<Symbol>)node.getData("liveG_out");
					if( GMalloc_in == null ) {
						PrintTools.println("==> Parallel region: " + pStmt, 0);
						Tools.exit("[Error in cudaMallocFreeAnalysis()] reachingGMalloc_in is null; " +
								"run reachingGMallocAnalysis before this analysis.");
					}
					if( liveG_out == null ) {
						PrintTools.println("==> Parallel region: " + pStmt, 0);
						Tools.exit("[Error in cudaMallocFreeAnalysis()] liveG_out is null; " +
								"run liveGVariableAnalysis before this analysis");
					}
					Set<Symbol> sharedVars = (Set<Symbol>)annot.get("shared");
					if( sharedVars != null ) {
						HashSet<String> noCudaFreeSet = new HashSet<String>();
						HashSet<String> noCudaMallocSet = new HashSet<String>();
						List<CudaAnnotation> cudaAnnots = pStmt.getAnnotations(CudaAnnotation.class);
						if( cudaAnnots != null ) {
							for( CudaAnnotation cannot : cudaAnnots ) {
								HashSet<String> dataSet = (HashSet<String>)cannot.get("nocudamalloc");
								if( dataSet != null ) {
									noCudaMallocSet.addAll(dataSet);
								}
								dataSet = (HashSet<String>)cannot.get("nocudafree");
								if( dataSet != null ) {
									noCudaFreeSet.addAll(dataSet);
								}
							}
						}
						Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(pStmt);
						Set<Symbol> defSyms = getBaseSymbols(tDefSyms);
						for( Symbol sVar: sharedVars ) {
							if( SymbolTools.isScalar(sVar) && !defSyms.contains(sVar) &&
									shrdSclrCachingOnSM ) {
								continue;
							}
							if( !GMalloc_in.contains(sVar) ) {
								if( !noCudaMallocSet.contains(sVar.getSymbolName()) ) {
									cudaMallocSet.add(sVar);
								}
							}
							if( !liveG_out.contains(sVar) ) {
								if( !noCudaFreeSet.contains(sVar.getSymbolName()) ) {
									cudaFreeSet.add(sVar);
								}
							}
						}
					}
					node.putData("cudaFreeSet", cudaFreeSet);
				} else {
					Tools.exit("[Error1 in cudaMallocFreeAnalysis()] Incorrect tag (kernelRegion) in a node: " + node);
				}
			}

		}
	}
	
	
	public static void residentGVariableAnalysis(CFGraph cfg) {
		boolean	shrdSclrCachingOnSM = false;
		String value = Driver.getOptionValue("shrdSclrCachingOnSM");
		if( value != null ) {
			shrdSclrCachingOnSM = true;
		}
		
		TreeMap work_list = new TreeMap();
	
		DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
		entry.putData("residentGVars_in", new HashSet<Symbol>());
		work_list.put(entry.getData("top-order"), entry);
		
		String currentRegion = new String("CPU");
	
		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.firstKey());
			
			String tag = (String)node.getData("tag");
			if( tag != null && tag.equals("barrier") ) {
				String type = (String)node.getData("type");
				if( type != null ) {
					if( type.equals("S2P") ) {
						currentRegion = new String("GPU");
					} else if( type.equals("P2S") ) {
						currentRegion = new String("CPU");
					}
				}
			}
	
			HashSet<Symbol> residentGVars_in = null;
			
	
			for ( DFANode pred : node.getPreds() )
			{
				Set<Symbol> pred_residentGVars_out = (Set<Symbol>)pred.getData("residentGVars_out");
				if ( residentGVars_in == null ) {
					if ( pred_residentGVars_out != null ) {
						residentGVars_in = new HashSet<Symbol>();
						residentGVars_in.addAll(pred_residentGVars_out);
					}
				} else {
					if ( pred_residentGVars_out != null ) {
						residentGVars_in.retainAll(pred_residentGVars_out);
					} 
				}
			}
	
			Set<Symbol> p_residentGVars_in = (Set<Symbol>)node.getData("residentGVars_in");
	
			if ( (residentGVars_in == null) || (p_residentGVars_in == null) || !residentGVars_in.equals(p_residentGVars_in) ) {
				node.putData("residentGVars_in", residentGVars_in);
					Set<Symbol> residentGVars_out = new HashSet<Symbol>();
				if( residentGVars_in != null ) {
					residentGVars_out.addAll(residentGVars_in);
				}
				Statement stmt = node.getData("pKernelRegion");
				if( stmt != null ) {
					OmpAnnotation annot = stmt.getAnnotation(OmpAnnotation.class, "parallel");
					if( annot != null ) {
						Set<Symbol> sharedVars = (Set<Symbol>)annot.get("shared");
						if( sharedVars != null ) {
							Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(stmt);
							Set<Symbol> defSyms = getBaseSymbols(tDefSyms);
							Set<String> constantSet = new HashSet<String>();
							CudaAnnotation cannot = stmt.getAnnotation(CudaAnnotation.class, "constant");
							if( cannot != null ) {
								constantSet.addAll((HashSet<String>)cannot.get("constant"));
							}
							for(Symbol sSym: sharedVars) {
								if( SymbolTools.isScalar(sSym) && !defSyms.contains(sSym) &&
										shrdSclrCachingOnSM ) {
									continue;
								} else if (constantSet.contains(sSym.getSymbolName())) {
									continue;
								} else {
									residentGVars_out.add(sSym);
								}
							}
							Set<Symbol> cudaFreeSet = node.getData("cudaFreeSet");
							if ( cudaFreeSet == null ) {
								Tools.exit("[ERRROR in residentGVariableAnalysis()] cudaFreeSet does not exist; " +
										"run cudaMallocFreeAnalysis() before this analysis.");
							} else {
								for(Symbol sSym: sharedVars) {
									if( cudaFreeSet.contains(sSym) ) {
										residentGVars_out.remove(sSym);
									}
								}
							}
							Set<Symbol> redSyms = findReductionSymbols(stmt);
							if( redSyms.size() > 0 ) {
								for(Symbol rSym : redSyms ) {
									residentGVars_out.remove(rSym);
								}
							}
						}
					} else {
						Tools.exit("[ERROR in residentGVariableAnalysis] Incorrect tag in a node: " + node);
					}
				}
				if( residentGVars_out.size() > 0 && currentRegion.equals("CPU") ) {
					Traversable ir = node.getData("ir");
					if( (ir != null) && (ir instanceof ExpressionStatement) ) {
						Expression expr = ((ExpressionStatement)ir).getExpression();
						if( expr instanceof FunctionCall ) {
							Set<Symbol> removeSet = new HashSet<Symbol>();
							for( Symbol sym: residentGVars_out ) {
								if( checkSharedVariableAccess(sym, expr) ) {
									removeSet.add(sym);
								}
							}
							residentGVars_out.removeAll(removeSet);
						}
					}
					if( ir != null ) {
						Set<Symbol> tDefSet = DataFlowTools.getDefSymbol(ir);
						Set<Symbol> defSet = getBaseSymbols(tDefSet);
						Set<Symbol> removeSet = new HashSet<Symbol>();
						for( Symbol sym: residentGVars_out ) {
							if( defSet.contains(sym) ) {
								removeSet.add(sym);
							}
						}
						residentGVars_out.removeAll(removeSet);
					}
				}
					
				node.putData("residentGVars_out", residentGVars_out);
	
				for ( DFANode succ : node.getSuccs() ) {
					work_list.put(succ.getData("top-order"), succ);
				}
			}
		}
	}

	
	static public void updateSymbols(Traversable t, HashSet<Symbol> old_set, HashSet<Symbol> new_set,
			boolean isShared)
	{
		VariableDeclaration sm_decl = null;
		VariableDeclarator v_declarator = null;
		Traversable tt = t;
		while( !(tt instanceof SymbolTable) ) {
			tt = tt.getParent();
		}
		Set<Symbol> accessedSymbols = null;
		if ( isShared ) {
			accessedSymbols = getIpAccessedVariableSymbols(t);
		} else {
			accessedSymbols = SymbolTools.getAccessedSymbols(t);
		}
		// Remove procedure symbols from accessedSymbols. //
		Set<Symbol> tSet = new HashSet<Symbol>();
		for( Symbol sm : accessedSymbols ) {
			if( (sm instanceof Procedure) || (sm instanceof ProcedureDeclarator) ) {
				tSet.add(sm);
			}
		}
		accessedSymbols.removeAll(tSet);
		for( Symbol sm : old_set) {
			boolean accessed = false;
			for( Symbol accSym : accessedSymbols ) {
				if( sm.getSymbolName().compareTo(accSym.getSymbolName()) == 0 ) {
					accessed = true;
					break;
				}
			}
			if( accessed ) {
				sm_decl = (VariableDeclaration)SymbolTools.findSymbol((SymbolTable)tt, 
						((VariableDeclarator)sm).getID());
				if( sm_decl == null ) {
					new_set.add(sm);
				} else {
					boolean found_sm = false;
					for( int i=0; i<sm_decl.getNumDeclarators(); i++ ) {
						Declarator tDeclr = sm_decl.getDeclarator(i);
						if( tDeclr instanceof VariableDeclarator ) {
							v_declarator = (VariableDeclarator)tDeclr;
							if( v_declarator.getSymbolName().compareTo(sm.getSymbolName()) == 0 ) {
								new_set.add(v_declarator);
								found_sm = true;
								break;
							}
						} else {
							break;
						}
					}
					if( !found_sm ) {
						new_set.add(sm);
					}
				}
			}
		}
	}
	
	
	static public void updateSymbols2(Traversable t, HashSet<Symbol> old_set, HashSet<Symbol> new_set,
			boolean isShared)
	{
		VariableDeclaration sm_decl = null;
		VariableDeclarator v_declarator = null;
		Traversable tt = t;
		while( !(tt instanceof SymbolTable) ) {
			tt = tt.getParent();
		}
		Set<Symbol> accessedSymbols = null;
		if ( isShared ) {
			accessedSymbols = getIpAccessedVariableSymbols(t);
		} else {
			accessedSymbols = SymbolTools.getAccessedSymbols(t);
		}
		Set<Symbol> tSet = new HashSet<Symbol>();
		for( Symbol sm : accessedSymbols ) {
			if( (sm instanceof Procedure) || (sm instanceof ProcedureDeclarator) ) {
				tSet.add(sm);
			}
		}
		accessedSymbols.removeAll(tSet);
		
		for( Symbol sm : old_set) {
			for( Symbol accSym : accessedSymbols ) {
				if( sm.getSymbolName().compareTo(accSym.getSymbolName()) == 0 ) {
					new_set.add(accSym);
					break;
				}
			}
		}
	}
	
	public static String symbolsToString(Collection<Symbol> symbols, String separator)
	{
		if ( symbols == null || symbols.size() == 0 )
			return "";

		StringBuilder str = new StringBuilder(80);

		Iterator<Symbol> iter = symbols.iterator();
		if ( iter.hasNext() )
		{
			str.append(iter.next().getSymbolName());
			while ( iter.hasNext() ) {
				str.append(separator+iter.next().getSymbolName());
			}
		}

		return str.toString();
	}
	
		public static Set<String> symbolsToStringSet(Collection<Symbol> symbols)
	{
		HashSet<String> strSet = new HashSet<String>();
		if ( symbols == null || symbols.size() == 0 )
			return strSet;


		Iterator<Symbol> iter = symbols.iterator();
		if ( iter.hasNext() )
		{
			strSet.add(iter.next().getSymbolName());
			while ( iter.hasNext() ) {
				strSet.add(iter.next().getSymbolName());
			}
		}

		return strSet;
	}
	

	public static HashMap<String, String> convert2StringMap(Map iMap) {
		HashMap<String, String> strMap = new HashMap<String, String>();
		Iterator iter = iMap.keySet().iterator();
		while(iter.hasNext()){
			Object key = iter.next();
			Object val = iMap.get(key);
			String sKey, sVal;
			if( key instanceof Symbol ) {
				sKey = ((Symbol)key).getSymbolName();
			} else {
				sKey = key.toString();
			}
			if( val instanceof Symbol ) {
				sVal = ((Symbol)val).getSymbolName();
			} else {
				sVal = val.toString();
			}
			strMap.put(sKey, sVal);
		}	
		return strMap;
	}
	
	
	public static Set<Symbol> findReductionSymbols(Traversable region) {
		HashMap redMap = null;
		HashSet<Symbol> redSet = new HashSet<Symbol>();
		List<OmpAnnotation> omp_annots = IRTools.collectPragmas(region, OmpAnnotation.class, "reduction");
		for (OmpAnnotation annot : omp_annots)
		{
			redMap = (HashMap)annot.get("reduction");
			for (String ikey : (Set<String>)(redMap.keySet())) {
				redSet.addAll( (HashSet<Symbol>)redMap.get(ikey) );
			}
		}
		return redSet;
	}
	

	public static Set<Symbol> findStaticSymbols(SymbolTable st) {
		HashSet<Symbol> staticSet = new HashSet<Symbol>();
		Set<Symbol> symbols = SymbolTools.getSymbols(st);
		for( Symbol sym : symbols ) {
			List types = sym.getTypeSpecifiers();
			if( types.contains(Specifier.STATIC) ) {
				staticSet.add(sym);
			}
		}
		return staticSet;
	}


	public static boolean ipaStaticDataCheck( CompoundStatement region ) {
		Boolean foundStaticData = false;
		List<FunctionCall> funcCalls = IRTools.getFunctionCalls(region); 
		for( FunctionCall calledProc : funcCalls ) {
			Procedure tProc = calledProc.getProcedure();
			if( tProc != null ) {
				foundStaticData = ipaStaticDataCheck(tProc.getBody());
				if( foundStaticData ) {
					break;
				}
			}
		}
	
		Set<Symbol> localSet = SymbolTools.getLocalSymbols((SymbolTable)region);
		for (Symbol sym : localSet)
		{
			if( foundStaticData ) {
				break;
			}
			// Check variable symbols only.
			if( (sym instanceof Procedure) || (sym instanceof ProcedureDeclarator) ) {
				continue;
			}
			List<Specifier> type_specs = sym.getTypeSpecifiers();
			for (Specifier spec : type_specs)
			{
				if ( spec.toString().compareTo("static")==0 )
				{
					foundStaticData = true;
					break;
				}
			}
		}
		return foundStaticData;
	}
	

	public static int isCalledByRef(Symbol sym, FunctionCall fCall) {
		int status = -1;
		Procedure calledProc = fCall.getProcedure();
		if( calledProc == null ) {
			status = -2; //Can't find the procedure for the function call.
		} else {
			boolean isPointerTypeArg = false;
			if( SymbolTools.isArray(sym) || SymbolTools.isPointer(sym) ) {
				isPointerTypeArg = true;
			}
			List argList = fCall.getArguments();
			List paramList = calledProc.getParameters();
			int list_size = argList.size();
			for( int i=0; i<list_size; i++ ) {
				Object arg = argList.get(i);
				Symbol paramSym = (Symbol)((VariableDeclaration)paramList.get(i)).getDeclarator(0);
				boolean isPointerTypeParam = false;
				if( SymbolTools.isArray(paramSym) || SymbolTools.isPointer(paramSym) ) {
					isPointerTypeParam = true;
				}
				if( arg instanceof Traversable ) {
					Set<Symbol> usedSyms = DataFlowTools.getUseSymbol((Traversable)arg);
					if( isPointerTypeParam && usedSyms.contains(sym) ) {
						if( isPointerTypeArg ) {
							status = i;
							break;
						} else if ( arg instanceof UnaryExpression ) {
							UnaryExpression uexp = (UnaryExpression)arg;
							if( uexp.getOperator().equals(UnaryOperator.ADDRESS_OF) ) {
								status = i;
								break;
							}
						}
					}
				} else {
					status = -3;
					break;
				}
			}
		}
		return status;
	}
	
	
	public static boolean ipaIsDefined(Symbol sym, Traversable t ) {
		boolean isDefined = false;
		Set<Symbol> defSet = DataFlowTools.getDefSymbol(t);
		if( defSet.contains(sym)) {
			isDefined = true;
		} else {
			List<FunctionCall> fCallList = IRTools.getFunctionCalls(t);
			for( FunctionCall fCall : fCallList ) {
				if( StandardLibrary.contains(fCall) ) {
					if( StandardLibrary.isSideEffectFree(fCall) ) {
						continue;
					} else {
						Set<Symbol> usedSyms = DataFlowTools.getUseSymbol(fCall);
						if( usedSyms.contains(sym) ) {
							isDefined = true;
							break;
						}
					}
				} else {
					Procedure proc = fCall.getProcedure();
					if( proc != null ) {
						int index = isCalledByRef(sym, fCall);
						if( index >= 0 ) {
							Symbol paramSym = (Symbol)((VariableDeclaration)proc.getParameter(index)).getDeclarator(0);
							isDefined = ipaIsDefined(paramSym, proc.getBody());
						} else if ( SymbolTools.isGlobal(sym) ) {
							isDefined = ipaIsDefined(sym, proc.getBody());
						}
						if( isDefined ) {
							break;
						}
					}
				} 
				
			}
		}
		return isDefined;
	}
	
	
	public static void annotateUserDirectives(Program program, 
			HashMap<String, HashMap<String, Object>> userDirectives) {
		boolean userDirectiveExists = false;
		String value = Driver.getOptionValue("maxNumOfCudaThreadBlocks");
		/* iterate to search for all Procedures */
		DepthFirstIterator proc_iter = new DepthFirstIterator(program);
		Set<Procedure> proc_list = (Set<Procedure>)(proc_iter.getSet(Procedure.class));
		for (Procedure proc : proc_list)
		{
			String procName = proc.getSymbolName();
			String kernelName = "";
			int kernelID = 0;
			/* Search for all OpenMP parallel regions in a given Procedure */
			List<OmpAnnotation>
			omp_annots = IRTools.collectPragmas(proc, OmpAnnotation.class, "parallel");
			for ( OmpAnnotation annot : omp_annots )
			{
				kernelName = "";
				Statement target_stmt = (Statement)annot.getAnnotatable();
				int eligibility = AnalysisTools.checkKernelEligibility(target_stmt);
				if (eligibility == 3) {
					// Check whether this parallel region is an omp-for loop.
					if( annot.containsKey("for") ) {
						// In the new annotation scheme, the above check is redundant.
						eligibility = 0;
					} else {
						// Check whether called functions have any omp-for loop.
						List<FunctionCall> funcCalls = IRTools.getFunctionCalls(target_stmt); 
						for( FunctionCall calledProc : funcCalls ) {
							Procedure tProc = calledProc.getProcedure();
							if( tProc != null ) {
								eligibility = AnalysisTools.checkKernelEligibility(tProc.getBody());
								if(  eligibility == 0 ) {
									break;
								}
							}
						}
					}
				} 
				if( eligibility == 0 ) {
					CudaAnnotation cAnnot = target_stmt.getAnnotation(CudaAnnotation.class, "ainfo");
					if( cAnnot == null ) {
						cAnnot = new CudaAnnotation("ainfo", "true");
						target_stmt.annotate(cAnnot);
					}
					cAnnot.put("procname", procName);
					cAnnot.put("kernelid", Integer.toString(kernelID));
					kernelName = kernelName.concat(procName).concat(Integer.toString(kernelID++));
					if( !userDirectives.isEmpty() ) {
						userDirectiveExists = true;
						Set<String> kernelSet = userDirectives.keySet();
						if( kernelSet.contains(kernelName) ) {
							HashMap<String, Object> directives = userDirectives.remove(kernelName);
							for( String clause : directives.keySet() ) {
								if( clause.equals("nogpurun") ) {
									cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, "nogpurun");
									if( cAnnot == null ) {
										cAnnot = new CudaAnnotation("nogpurun", "true");
										target_stmt.annotate(cAnnot);
									}
									break; //Ignore all remaining clauese for this kernel region.
								}
								Object uObj = directives.get(clause);
								cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, clause);
								if( cAnnot == null ) {
									cAnnot = new CudaAnnotation("gpurun", "true");
									cAnnot.put(clause, uObj);
									target_stmt.annotate(cAnnot);
								} else {
									Object fObj = cAnnot.get(clause);
									if( fObj instanceof Set ) {
										((Set<String>)fObj).addAll((Set<String>)uObj);
									} else {
										cAnnot.put(clause, uObj);
									}
								}
							
								if( clause.equals("c2gmemtr") ) {
									cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, "noc2gmemtr");
									if( cAnnot != null ) {
										Set<String> sSet = cAnnot.get("noc2gmemtr");
										sSet.removeAll((Set<String>)uObj);
									}
								}else if( clause.equals("noc2gmemtr") ) {
									cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, "c2gmemtr");
									if( cAnnot != null ) {
										Set<String> sSet = cAnnot.get("c2gmemtr");
										sSet.removeAll((Set<String>)uObj);
									}
								}else if( clause.equals("g2cmemtr") ) {
									cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, "nog2cmemtr");
									if( cAnnot != null ) {
										Set<String> sSet = cAnnot.get("nog2cmemtr");
										sSet.removeAll((Set<String>)uObj);
									}
								}else if( clause.equals("nog2cmemtr") ) {
									cAnnot =  target_stmt.getAnnotation(CudaAnnotation.class, "g2cmemtr");
									if( cAnnot != null ) {
										Set<String> sSet = cAnnot.get("g2cmemtr");
										sSet.removeAll((Set<String>)uObj);
									}
								}
							}
						}
					}
					if( value != null ) {
						cAnnot = target_stmt.getAnnotation(CudaAnnotation.class, "maxnumofblocks");
						if( cAnnot == null ) {
							cAnnot = new CudaAnnotation("gpurun", "true");
							cAnnot.put("maxnumofblocks", value);
							target_stmt.annotate(cAnnot);
						}
					}
				}
			}
		}
		if( userDirectiveExists ) {
			if( !userDirectives.isEmpty() ) {
				Set<String> kernelSet = userDirectives.keySet();
				PrintTools.println("[WARNING in annotateUserDirectives()] user directives for the following" +
						" set of kernels can not be applicable: " + PrintTools.collectionToString(kernelSet, ","), 0);
			}
		}
	}
	
	public static boolean isCudaCall(FunctionCall fCall) {
		if ( fCall == null )
			return false;

		Set<String> cudaCalls = new HashSet<String>(Arrays.asList(
				"CUDA_SAFE_CALL","cudaFree","cudaMalloc","cudaMemcpy",
				"cudaMallocPitch","tex1Dfetch","cudaBindTexture", "cudaMemcpy2D"
		));

		if ( cudaCalls.contains((fCall.getName()).toString()) ) {
			return true;
		}
		return false;
	}
	
	public static boolean isKernelFunction(Procedure proc) {
		if( proc == null ) {
			return false;
		}
		List return_type = proc.getReturnType();
		if( return_type.contains(CUDASpecifier.CUDA_DEVICE) 
				|| return_type.contains(CUDASpecifier.CUDA_GLOBAL) ) {
			return true;
		} else {
			return false;
		}
	}
	
	  /**
	   * Returns true if there is a KernelFunctionCall within the traversable.
	   *
	   * @param t  traversable object to be searched.
	   * @return true if {@code t} contains a function call.
	   */
	  public static boolean containsKernelFunctionCall(Traversable t)
	  {
	    if ( t == null ) return false;

	    DepthFirstIterator iter = new DepthFirstIterator(t);
	    while ( iter.hasNext() )
	    {
	      Object o = iter.next();
	      if (o instanceof KernelFunctionCall)
	      {
	        return true;
	      }
	    }
	    return false;
	  }
	
	
	public static Set<Symbol> getAccessedVariables(Statement stmt)
	{
		Set<Symbol> set = SymbolTools.getAccessedSymbols(stmt);
		HashSet<Symbol> ret = new HashSet<Symbol> ();
		for (Symbol symbol : set)
		{
			if( symbol instanceof VariableDeclarator ) {
				if( !isClassMember((VariableDeclarator)symbol) ) {
					ret.add(symbol);
				}
			} else if( symbol instanceof AccessSymbol ) {
				Symbol base = ((AccessSymbol)symbol).getIRSymbol();
				if( base != null ) {
					ret.add(base);
				}
			} else if( symbol instanceof NestedDeclarator ){
				//FIXME: How to handle NestedDeclarator?
				ret.add(symbol);
			}
		}
		return ret;
	}
}
