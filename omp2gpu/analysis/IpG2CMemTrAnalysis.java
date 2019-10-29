package omp2gpu.analysis;

import omp2gpu.hir.CudaAnnotation;
import omp2gpu.transforms.SplitOmpPRegion;
import omp2gpu.transforms.TransformTools;
import cetus.analysis.AnalysisPass;
import cetus.analysis.CFGraph;
import cetus.analysis.DFANode;
import cetus.exec.Driver;
import cetus.hir.AccessSymbol;
import cetus.hir.Annotatable;
import cetus.hir.AnnotationStatement;
import cetus.hir.BreadthFirstIterator;
import cetus.hir.CommentAnnotation;
import cetus.hir.CompoundStatement;
import cetus.hir.Declaration;
import cetus.hir.Declarator;
import cetus.hir.DepthFirstIterator;
import cetus.hir.Expression;
import cetus.hir.ExpressionStatement;
import cetus.hir.FlatIterator;
import cetus.hir.FunctionCall;
import cetus.hir.IDExpression;
import cetus.hir.Identifier;
import cetus.hir.NameID;
import cetus.hir.OmpAnnotation;
import cetus.hir.Procedure;
import cetus.hir.ProcedureDeclarator;
import cetus.hir.Program;
import cetus.hir.Specifier;
import cetus.hir.Statement;
import cetus.hir.SymbolTools;
import cetus.hir.Tools;
import cetus.hir.DataFlowTools;
import cetus.hir.IRTools;
import cetus.hir.PrintTools;
import cetus.hir.Symbol;
import cetus.hir.StandardLibrary;
import cetus.hir.TranslationUnit;
import cetus.hir.Traversable;
import cetus.hir.VariableDeclaration;
import cetus.hir.VariableDeclarator;

import java.util.HashSet;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.Iterator;


public class IpG2CMemTrAnalysis extends AnalysisPass {
	private boolean assumeNonZeroTripLoops;
	private HashMap<Symbol, Symbol> l2gGVMap;
	private Stack<HashMap<Symbol, Symbol>> l2gGVMapStack;
	private HashMap<Procedure, AnalysisTools.REGIONMAP> visitedProcs1;
	private HashMap<Procedure, HashSet<Symbol>> visitedProcs2;
	private String currentRegion;
	private Procedure main;
	private Set<Symbol> targetSymbols;
	private int MemTrOptLevel = 2;

	public IpG2CMemTrAnalysis(Program program) {
		super(program);
	}

	public String getPassName() {
		return new String("[IpG2CMemTrAnalysis]");
	}

	public void start() {
		main = null;
		l2gGVMapStack = new Stack<HashMap<Symbol, Symbol>>();
		String value = Driver.getOptionValue("useGlobalGMalloc");
		if( value == null ) {
			PrintTools.println("[WARNING in IpG2CMemTrAnalysis()] " +
					"to run this analysis, useGlobalGMalloc option should be on; " +
					"ignore this analysis!", 0);
			return;
		}
		for ( Traversable tu : program.getChildren() ) {
			if( main == null ) {
				BreadthFirstIterator iter = new BreadthFirstIterator(tu);
				iter.pruneOn(Procedure.class);

				for (;;)
				{
					Procedure proc = null;

					try {
						proc = (Procedure)iter.next(Procedure.class);
					} catch (NoSuchElementException e) {
						break;
					}

					String name = proc.getName().toString();

					/* f2c code uses MAIN__ */
					if (name.equals("main") || name.equals("MAIN__")) {
						main = proc;
						break;
					}
				}
			} else {
				break;
			}
		}
		if( main == null ) {
			Tools.exit("[ERROR in IpG2CMemTrAnalysis] can't find a main()");
		}
		AnalysisTools.markIntervalForKernelRegions(program);
		assumeNonZeroTripLoops = false;
		value = Driver.getOptionValue("assumeNonZeroTripLoops");
		if( value != null ) {
			assumeNonZeroTripLoops = true;
		}
		value = Driver.getOptionValue("cudaMemTrOptLevel");
		if( value != null ) {
			MemTrOptLevel = Integer.valueOf(value).intValue();
		}
		targetSymbols = AnalysisTools.getIpOmpSharedVariables(main);
		PrintTools.println("Symbols of interest: " + AnalysisTools.symbolsToString(targetSymbols, ","), 2);
		
		currentRegion = new String("CPU");
		visitedProcs1 = new HashMap<Procedure, AnalysisTools.REGIONMAP>();
		AnalysisTools.REGIONMAP dummySet1 = new AnalysisTools.REGIONMAP();
		gMustDefAnalysis(main, dummySet1, null, currentRegion, false);
		l2gGVMapStack.clear();
		currentRegion = new String("CPU");
		visitedProcs2 = new HashMap<Procedure, HashSet<Symbol>>();
		HashSet<Symbol> dummySet2 = new HashSet<Symbol>();
		gLiveCVarAnalysis(main, dummySet2, null, currentRegion, false);
		
		SplitOmpPRegion.cleanExtraBarriers(program, false);

	}
	
	private boolean gMustDefAnalysis(Procedure proc, AnalysisTools.REGIONMAP MustDefSet, 
			FunctionCall funcCall, String currentRegion, boolean callerContainsStatic) {
		boolean containsStaticData = false;
		boolean notClonable = false;
		Procedure clonedProc = null;
		LinkedList<VariableDeclaration> clonedProcDecls = new LinkedList<VariableDeclaration>();
		FunctionCall orgFCall = funcCall;
		FunctionCall newFCall = null;
		boolean AnnotationAdded = false;
		l2gGVMap = new HashMap<Symbol, Symbol>();
		if( proc != main ) {
			Set<Symbol> staticSyms = AnalysisTools.findStaticSymbols(proc.getBody());
			if( staticSyms.size() > 0 ) {
				containsStaticData = true;
			}
			if( callerContainsStatic || containsStaticData ) {
				notClonable = true;
			}
		}
		if( visitedProcs1.containsKey(proc) ) {
			AnalysisTools.REGIONMAP prevContext = visitedProcs1.get(proc);
			if( !prevContext.equals(MustDefSet) ) {
				boolean cloneProcedure = false;
				boolean foundSameContextCall = false;
				int k = 0;
				if( notClonable ) {
					prevContext = prevContext.intersectWith(MustDefSet, "conditional");
					visitedProcs1.put(proc, prevContext);
				} else {
					HashSet<String> procedureSet = AnalysisTools.getProcedureSet(program);
					Set<Procedure> procSet = visitedProcs1.keySet();
					HashMap<String, Procedure> visitedProcMap = new HashMap<String, Procedure>();
					for( Procedure tProc : procSet ) {
						visitedProcMap.put(tProc.getSymbolName(), tProc);
					}
					String proc_name = proc.getSymbolName();
					int ind = proc_name.lastIndexOf("_cloned");
					if( ind != -1 ) {
						proc_name = proc_name.substring(0,ind) + "_cloned";
					} else {
						proc_name = proc_name + "_cloned";
					}
					String new_proc_name = proc_name + k++;
					while( k<=visitedProcMap.size() ) {
						Procedure tProc = visitedProcMap.get(new_proc_name);
						if( tProc != null ) {
							prevContext = visitedProcs1.get(tProc);
							if( prevContext.equals(MustDefSet) ) {
								proc = tProc;
								cloneProcedure = false;
								foundSameContextCall = true;
								break;
							}
						}
						new_proc_name = proc_name + k++;
					}
					if( foundSameContextCall ) {
						if( funcCall != null ) {
							FunctionCall new_funcCall = new FunctionCall(new NameID(new_proc_name));
							List<Expression> argList = (List<Expression>)funcCall.getArguments();
							if( argList != null ) {
								for( Expression exp : argList ) {
									new_funcCall.addArgument(exp.clone());
								}
							}
							funcCall.swapWith(new_funcCall);
						}
					} else {
						cloneProcedure = true;
					}
					if( cloneProcedure ) {
						k = 0;
						while( true ) {
							new_proc_name = proc_name + k++;
							if( !procedureSet.contains(new_proc_name) ) {
								break;
							}
						}
						List<Specifier> return_types = proc.getReturnType();
						List<VariableDeclaration> oldParamList = 
							(List<VariableDeclaration>)proc.getParameters();
						CompoundStatement body = (CompoundStatement)proc.getBody().clone();
						Procedure new_proc = new Procedure(return_types,
								new ProcedureDeclarator(new NameID(new_proc_name),
										new LinkedList()), body);	
						if( oldParamList != null ) {
							for( VariableDeclaration param : oldParamList ) {
								Symbol param_declarator = (Symbol)param.getDeclarator(0);
								VariableDeclaration cloned_decl = (VariableDeclaration)param.clone();
								Identifier paramID = new Identifier(param_declarator);
								Identifier cloned_ID = new Identifier((Symbol)cloned_decl.getDeclarator(0));
								new_proc.addDeclaration(cloned_decl);
								IRTools.replaceAll((Traversable) body, paramID, cloned_ID);
							}
						}
						TranslationUnit tu = (TranslationUnit)proc.getParent();
						FlatIterator Fiter = new FlatIterator(program);
						while (Fiter.hasNext())
						{
							TranslationUnit cTu = (TranslationUnit)Fiter.next();
							BreadthFirstIterator iter = new BreadthFirstIterator(cTu);
							iter.pruneOn(ProcedureDeclarator.class);
							for (;;)
							{
								ProcedureDeclarator procDeclr = null;

								try {
									procDeclr = (ProcedureDeclarator)iter.next(ProcedureDeclarator.class);
								} catch (NoSuchElementException e) {
									break;
								}
								if( procDeclr.getID().equals(proc.getName()) ) {
									VariableDeclaration procDecl = (VariableDeclaration)procDeclr.getParent();
									VariableDeclaration newProcDecl = 
										new VariableDeclaration(procDecl.getSpecifiers(), new_proc.getDeclarator().clone());
									cTu.addDeclarationAfter(procDecl, newProcDecl);
									clonedProcDecls.add(newProcDecl);
									break;
								}
							}
						}
						tu.addDeclarationAfter(proc, new_proc);
						clonedProc = new_proc;
						SymbolTools.linkSymbol(new_proc);
						TransformTools.updateAnnotationsInRegion(new_proc, true);
						DepthFirstIterator itr = new DepthFirstIterator(new_proc);
						while(itr.hasNext())
						{
							Object obj = itr.next();

							if ( (obj instanceof Annotatable) && (obj instanceof Statement) )
							{
								Annotatable at = (Annotatable)obj;
								List<CudaAnnotation> aList = at.getAnnotations(CudaAnnotation.class);
								if( aList != null ) {
									List<CudaAnnotation> newList = new LinkedList<CudaAnnotation>();
									for( CudaAnnotation cAnnot : aList ) {
										cAnnot.remove("mustdefset");
										if( !cAnnot.isEmpty() ) {
											newList.add(cAnnot);
										}
										at.removeAnnotations(CudaAnnotation.class);
										if( newList.size() > 0 ) {
											for( CudaAnnotation newAnnot : newList ) {
												at.annotate(newAnnot);
											}
										} 
									}
								}
							}
						}

						proc = new_proc;
					}
					if( funcCall != null ) {
						FunctionCall new_funcCall = new FunctionCall(new NameID(new_proc_name));
						List<Expression> argList = (List<Expression>)funcCall.getArguments();
						if( argList != null ) {
							for( Expression exp : argList ) {
								new_funcCall.addArgument(exp.clone());
							}
						}
						funcCall.swapWith(new_funcCall);
						newFCall = new_funcCall;
					}
					visitedProcs1.put(proc, (AnalysisTools.REGIONMAP)MustDefSet.clone());
				}
			}
		} else {
			visitedProcs1.put(proc, (AnalysisTools.REGIONMAP)MustDefSet.clone());
		}
		
		PrintTools.println("[gMustDefAnalysis] analyze " + proc.getSymbolName(), 2);
		
		OCFGraph.setNonZeroTripLoops(assumeNonZeroTripLoops);
		CFGraph cfg = new OCFGraph(proc, null);
		
		cfg.topologicalSort(cfg.getNodeWith("stmt", "ENTRY"));
		
		TreeMap work_list = new TreeMap();
		
		DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
		AnalysisTools.REGIONMAP gMustDefSet_in = (AnalysisTools.REGIONMAP)MustDefSet.clone();
		AnalysisTools.REGIONMAP gMustDefSet_out = (AnalysisTools.REGIONMAP)MustDefSet.clone();
		entry.putData("gMustDefSet_in", gMustDefSet_in);
		entry.putData("gMustDefSet_out", gMustDefSet_out);
		for ( DFANode succ : entry.getSuccs() ) {
			work_list.put(succ.getData("top-order"), succ);
		}
		
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
	
			gMustDefSet_in = null;
			
			DFANode temp = (DFANode)node.getData("back-edge-from");
			for ( DFANode pred : node.getPreds() )
			{
				AnalysisTools.REGIONMAP pred_gMustDefSet_out = pred.getData("gMustDefSet_out");
				if ( gMustDefSet_in == null ) {
					if ( pred_gMustDefSet_out != null ) {
						gMustDefSet_in = (AnalysisTools.REGIONMAP)pred_gMustDefSet_out.clone();
					}
				} else {
					// Calculate intersection of previous nodes.
					if ( pred_gMustDefSet_out != null ) {
						if( (temp != null) && (temp == pred) ) {
							gMustDefSet_in = gMustDefSet_in.unionWith(pred_gMustDefSet_out, "multiple");
						} else {
							gMustDefSet_in = gMustDefSet_in.intersectWith(pred_gMustDefSet_out, "conditional");
						}
					} 
				}
			}
	
			AnalysisTools.REGIONMAP p_gMustDefSet_in = node.getData("gMustDefSet_in");
	
			if ( (gMustDefSet_in == null) || (p_gMustDefSet_in == null) || !gMustDefSet_in.equals(p_gMustDefSet_in) ) {
				node.putData("gMustDefSet_in", gMustDefSet_in);

				gMustDefSet_out = new AnalysisTools.REGIONMAP();

				Traversable ir = node.getData("ir");
				if( ir != null ) {
					Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(ir);
					Set<Symbol> defSyms = AnalysisTools.getBaseSymbols(tDefSyms);
					for( Symbol sym : defSyms ) {
						Symbol gSym = null;
						if( l2gGVMap.containsKey(sym) ) {
							gSym = l2gGVMap.get(sym);
						} else {
							List symInfo = AnalysisTools.findOrgSymbol(sym, proc);
							if( symInfo.size() == 2 ) {
								gSym = (Symbol)symInfo.get(0);
								l2gGVMap.put(sym, gSym);
							} 
						}
						if( (gSym != null) && targetSymbols.contains(gSym) ) {
							gMustDefSet_out.put(gSym, currentRegion);
						}
					}
				}
				if( gMustDefSet_in != null ) {
					gMustDefSet_out = gMustDefSet_out.overwritingUnionWith(gMustDefSet_in);
				}

				if( (ir != null) && (ir instanceof ExpressionStatement) ) {
					ExpressionStatement estmt = (ExpressionStatement)ir;
					Expression expr = estmt.getExpression();
					List<FunctionCall> fcalls = IRTools.getFunctionCalls(expr);
					if( fcalls !=null ) {
						for( FunctionCall funCall : fcalls ) {
							if( !StandardLibrary.contains(funCall) ) {
								Procedure calledProc = funCall.getProcedure();
								if( calledProc != null ) {
									l2gGVMapStack.push(l2gGVMap);
									if( gMustDefAnalysis(calledProc, gMustDefSet_out, funCall, currentRegion, notClonable ) ) {
										AnnotationAdded = true;
									}
									l2gGVMap = l2gGVMapStack.pop();
								}
							}
						}
					}
				}
					
				node.putData("gMustDefSet_out", gMustDefSet_out);
	
				for ( DFANode succ : node.getSuccs() ) {
					work_list.put(succ.getData("top-order"), succ);
				}
			}
		}
		MustDefSet.clear();
		List<DFANode> exit_nodes = cfg.getExitNodes();
		boolean firstNode = true;
		for( DFANode exit_node : exit_nodes ) {
			AnalysisTools.REGIONMAP lrmap;
			lrmap =	(AnalysisTools.REGIONMAP)exit_node.getData("gMustDefSet_out");
			if( lrmap == null ) {
				PrintTools.println("[WARNING in IpG2CMemTrAnalysis()] the following exit node does not have gMustDefSet_out set:\n" +
						exit_node.toString() + "\n", 1);
			} else {
				if( firstNode ) {
					MustDefSet.addAll(lrmap, "multiple");
					firstNode = false;
				} else {
					MustDefSet.retainAll(lrmap, "conditional");
				}
			}
		}
		
		Iterator<DFANode> iter = cfg.iterator();
		while ( iter.hasNext() )
		{
			DFANode node = iter.next();
			Object obj = node.getData("tag");
			if( obj instanceof String ) {
				String tag = (String)obj;
				if( !tag.equals("barrier") ) {
					continue;
				}
			} else {
				continue;
			}
			Statement IRStmt = null;
			String type = (String)node.getData("type");
			if( !type.equals("P2S") ) {
				continue;
			}
			obj = node.getData("ir");
			if( obj instanceof Statement ) {
				IRStmt = (Statement)obj;
			} else {
				continue;
			}
			if( IRStmt != null ) {
				HashMap<String, String> gMustDefSet = null;
				CudaAnnotation mustDefAnnot = IRStmt.getAnnotation(CudaAnnotation.class, "mustdefset");
				if( mustDefAnnot != null ) {
					gMustDefSet = mustDefAnnot.get("mustdefset");
				}
				AnalysisTools.REGIONMAP tCudagMustDefSet = node.getData("gMustDefSet_out");
				HashMap<String, String> cudagMustDefSet = AnalysisTools.convert2StringMap(tCudagMustDefSet);
				if( !cudagMustDefSet.isEmpty() ) {
					if( notClonable ) {
						if( mustDefAnnot != null ) {
							AnalysisTools.REGIONMAP.retainAllS(gMustDefSet, cudagMustDefSet, "conditional");
						}
					} else {
						if( mustDefAnnot == null ) {
							AnnotationAdded = true;
							mustDefAnnot = new CudaAnnotation();
							mustDefAnnot.put("mustdefset", (HashMap<String, String>)cudagMustDefSet.clone());
							IRStmt.annotate(mustDefAnnot);
						} else {
							if( AnalysisTools.REGIONMAP.addAllS(gMustDefSet, cudagMustDefSet, "multiple") ) {
								AnnotationAdded = true;
							}
						}
					}
				} else if( notClonable ) {
					if( mustDefAnnot != null ) {
						mustDefAnnot.remove("mustdefset");
					}
				}
			}
		}
		
		if( (clonedProc != null) && (!AnnotationAdded) ) {
			PrintTools.println("[gMustDefAnalysis] delete cloned procedure: " + clonedProc.getSymbolName(), 1);
			Traversable tu = clonedProc.getParent();
			tu.removeChild(clonedProc);
			newFCall.swapWith(orgFCall);
			if( !clonedProcDecls.isEmpty() ) {
				for( VariableDeclaration cProcDecl : clonedProcDecls ) {
					Traversable pTu = cProcDecl.getParent();
					TransformTools.removeChild(pTu, cProcDecl);
				}
			}
			visitedProcs1.remove(clonedProc);
		}
		
		PrintTools.println("[gMustDefAnalysis] analysis of " + proc.getSymbolName() + " ended", 2);
		return AnnotationAdded;
	}
	
	private boolean gLiveCVarAnalysis(Procedure proc, HashSet<Symbol> LiveCVars, 
			FunctionCall funcCall, String currentRegion, boolean callerContainsStatic) {
		boolean containsStaticData = false;
		boolean notClonable = false;
		Procedure clonedProc = null;
		LinkedList<VariableDeclaration> clonedProcDecls = new LinkedList<VariableDeclaration>();
		FunctionCall orgFCall = funcCall;
		FunctionCall newFCall = null;
		boolean AnnotationAdded = false;
		l2gGVMap = new HashMap<Symbol, Symbol>();
		if( proc != main ) {
			Set<Symbol> staticSyms = AnalysisTools.findStaticSymbols(proc.getBody());
			if( staticSyms.size() > 0 ) {
				containsStaticData = true;
			}
			if( callerContainsStatic || containsStaticData ) {
				notClonable = true;
			}
		}
		if( visitedProcs2.containsKey(proc) ) {
			HashSet<Symbol> prevContext = visitedProcs2.get(proc);
			if( !prevContext.equals(LiveCVars) ) {
				boolean cloneProcedure = false;
				boolean foundSameContextCall = false;
				int k = 0;
				if( notClonable ) {
					prevContext.retainAll(LiveCVars);
					visitedProcs2.put(proc, prevContext);
				} else {
					HashSet<String> procedureSet = AnalysisTools.getProcedureSet(program);
					Set<Procedure> procSet = visitedProcs2.keySet();
					HashMap<String, Procedure> visitedProcMap = new HashMap<String, Procedure>();
					for( Procedure tProc : procSet ) {
						visitedProcMap.put(tProc.getSymbolName(), tProc);
					}
					String proc_name = proc.getSymbolName();
					int ind = proc_name.lastIndexOf("_cloned");
					if( ind != -1 ) {
						proc_name = proc_name.substring(0,ind) + "_cloned";
					} else {
						proc_name = proc_name + "_cloned";
					}
					String new_proc_name = proc_name + k++;
					while( k<=visitedProcMap.size() ) {
						Procedure tProc = visitedProcMap.get(new_proc_name);
						if( tProc != null ) {
							prevContext = visitedProcs2.get(tProc);
							if( prevContext.equals(LiveCVars) ) {
								proc = tProc;
								cloneProcedure = false;
								foundSameContextCall = true;
								break;
							}
						}
						new_proc_name = proc_name + k++;
					}
					if( foundSameContextCall ) {
						if( funcCall != null ) {
							FunctionCall new_funcCall = new FunctionCall(new NameID(new_proc_name));
							List<Expression> argList = (List<Expression>)funcCall.getArguments();
							if( argList != null ) {
								for( Expression exp : argList ) {
									new_funcCall.addArgument(exp.clone());
								}
							}
							funcCall.swapWith(new_funcCall);
						}
					} else {
						cloneProcedure = true;
					}
					if( cloneProcedure ) {
						k = 0;
						while( true ) {
							new_proc_name = proc_name + k++;
							if( !procedureSet.contains(new_proc_name) ) {
								break;
							}
						}
						List<Specifier> return_types = proc.getReturnType();
						List<VariableDeclaration> oldParamList = 
							(List<VariableDeclaration>)proc.getParameters();
						CompoundStatement body = (CompoundStatement)proc.getBody().clone();
						Procedure new_proc = new Procedure(return_types,
								new ProcedureDeclarator(new NameID(new_proc_name),
										new LinkedList()), body);	
						if( oldParamList != null ) {
							for( VariableDeclaration param : oldParamList ) {
								Symbol param_declarator = (Symbol)param.getDeclarator(0);
								VariableDeclaration cloned_decl = (VariableDeclaration)param.clone();
								Identifier paramID = new Identifier(param_declarator);
								Identifier cloned_ID = new Identifier((Symbol)cloned_decl.getDeclarator(0));
								new_proc.addDeclaration(cloned_decl);
								IRTools.replaceAll((Traversable) body, paramID, cloned_ID);
							}
						}
						TranslationUnit tu = (TranslationUnit)proc.getParent();
						{
							TranslationUnit cTu = (TranslationUnit)Fiter.next();
							BreadthFirstIterator iter = new BreadthFirstIterator(cTu);
							iter.pruneOn(ProcedureDeclarator.class);
							for (;;)
							{
								ProcedureDeclarator procDeclr = null;

								try {
									procDeclr = (ProcedureDeclarator)iter.next(ProcedureDeclarator.class);
								} catch (NoSuchElementException e) {
									break;
								}
								if( procDeclr.getID().equals(proc.getName()) ) {
									VariableDeclaration procDecl = (VariableDeclaration)procDeclr.getParent();
									VariableDeclaration newProcDecl = 
										new VariableDeclaration(procDecl.getSpecifiers(), new_proc.getDeclarator().clone());
									cTu.addDeclarationAfter(procDecl, newProcDecl);
									clonedProcDecls.add(newProcDecl);
									break;
								}
							}
						}
						tu.addDeclarationAfter(proc, new_proc);
						clonedProc = new_proc;
						SymbolTools.linkSymbol(new_proc);
						TransformTools.updateAnnotationsInRegion(new_proc, true);
						DepthFirstIterator itr = new DepthFirstIterator(new_proc);
						while(itr.hasNext())
						{
							Object obj = itr.next();

							if ( (obj instanceof Annotatable) && (obj instanceof Statement) )
							{
								Annotatable at = (Annotatable)obj;
								List<CudaAnnotation> aList = at.getAnnotations(CudaAnnotation.class);
								if( aList != null ) {
									List<CudaAnnotation> newList = new LinkedList<CudaAnnotation>();
									for( CudaAnnotation cAnnot : aList ) {
										cAnnot.remove("nog2cmemtr");
										if( !cAnnot.isEmpty() ) {
											newList.add(cAnnot);
										}
									}
									at.removeAnnotations(CudaAnnotation.class);
									if( newList.size() > 0 ) {
										for( CudaAnnotation newAnnot : newList ) {
											at.annotate(newAnnot);
										}
									} 
								}
							}
						}

						proc = new_proc;
					}
					if( funcCall != null ) {
						FunctionCall new_funcCall = new FunctionCall(new NameID(new_proc_name));
						List<Expression> argList = (List<Expression>)funcCall.getArguments();
						if( argList != null ) {
							for( Expression exp : argList ) {
								new_funcCall.addArgument(exp.clone());
							}
						}
						funcCall.swapWith(new_funcCall);
						newFCall = new_funcCall;
					}
					visitedProcs2.put(proc, (HashSet<Symbol>)LiveCVars.clone());
				}
			}
		} else {
			visitedProcs2.put(proc, (HashSet<Symbol>)LiveCVars.clone());
		}
		
		PrintTools.println("[gLiveCVarAnalysis] analyze " + proc.getSymbolName(), 2);
		
		OCFGraph.setNonZeroTripLoops(assumeNonZeroTripLoops);
		CFGraph cfg = new OCFGraph(proc, null);
		
		cfg.topologicalSort(cfg.getNodeWith("stmt", "ENTRY"));
		
		AnalysisTools.annotateBarriers(proc, cfg);
		
		TreeMap work_list = new TreeMap();
		
		List<DFANode> exit_nodes = cfg.getExitNodes();
		if (exit_nodes.size() > 1)
		{
			PrintTools.println("[WARNING in gLiveCVarAnalysis] multiple exits in the program", 1);
		}

		HashSet<Symbol> gLiveCVars_in = null;
		HashSet<Symbol> gLiveCVars_out = null;
		for ( DFANode exit_node : exit_nodes ) {
			gLiveCVars_out = (HashSet<Symbol>)LiveCVars.clone();
			exit_node.putData("gLiveCVars_out", gLiveCVars_out);
			work_list.put(exit_node.getData("top-order"), exit_node);
		}

		// Do iterative steps
		while ( !work_list.isEmpty() )
		{
			DFANode node = (DFANode)work_list.remove(work_list.lastKey());
			
			String tag = (String)node.getData("tag");
			// Check whether the node is in the kernel region or not.
			if( tag != null && tag.equals("barrier") ) {
				String type = (String)node.getData("type");
				if( type != null ) {
					if( type.equals("S2P") ) {
						currentRegion = new String("CPU");
					} else if( type.equals("P2S") ) {
						currentRegion = new String("GPU");
					}
				}
			}
	

					Set<Symbol> tDefSyms = DataFlowTools.getDefSymbol(ir);
					Set<Symbol> defSyms = AnalysisTools.getBaseSymbols(tDefSyms);
					Set<Symbol> gDefSyms = new HashSet<Symbol>();
					for( Symbol sym : defSyms ) {
						Symbol gSym = null;
						if( l2gGVMap.containsKey(sym) ) {
							gSym = l2gGVMap.get(sym);
						} else {
							List symInfo = AnalysisTools.findOrgSymbol(sym, proc);
							if( symInfo.size() == 2 ) {
								gSym = (Symbol)symInfo.get(0);
								l2gGVMap.put(sym, gSym);
							} 
						}
						if( (gSym != null) && targetSymbols.contains(gSym) ) {
							gDefSyms.add(gSym);
						}
					}

					if( currentRegion.equals("CPU") ) {
						if( gLiveCVars_out.isEmpty() ) {
							gLiveCVars_in.addAll(gUseSyms);
						} else {
							gLiveCVars_in.addAll(gLiveCVars_out);
							gLiveCVars_in.removeAll(gDefSyms);
							gLiveCVars_in.addAll(gUseSyms);
						}
					} else {
						gLiveCVars_in.addAll(gLiveCVars_out);
						gLiveCVars_in.removeAll(gDefSyms);
					}

					if( (ir != null) && (ir instanceof ExpressionStatement) ) {
						ExpressionStatement estmt = (ExpressionStatement)ir;
						Expression expr = estmt.getExpression();
						List<FunctionCall> fcalls = IRTools.getFunctionCalls(expr);
						if( fcalls !=null ) {
							for( FunctionCall funCall : fcalls ) {
								if( !StandardLibrary.contains(funCall) ) {
									Procedure calledProc = funCall.getProcedure();
									if( calledProc != null ) {
										l2gGVMapStack.push(l2gGVMap);
										if( gLiveCVarAnalysis(calledProc, gLiveCVars_in, funCall, currentRegion, notClonable) ) {
											AnnotationAdded = true;
										}
										l2gGVMap = l2gGVMapStack.pop();
									}
								}
							}
						}
					}
				} else {
					gLiveCVars_in.addAll(gLiveCVars_out);
				}

				node.putData("gLiveCVars_in", gLiveCVars_in);

				for ( DFANode pred : node.getPreds() ) {
					work_list.put(pred.getData("top-order"), pred);
				}
			}
		}
		LiveCVars.clear();
		List<DFANode> entry_nodes = cfg.getEntryNodes();
		for( DFANode entry : entry_nodes ) {
			LiveCVars.addAll((HashSet<Symbol>)entry.getData("gLiveCVars_in"));
		}
		
		Iterator<DFANode> iter = cfg.iterator();
		while ( iter.hasNext() )
		{
			DFANode node = iter.next();
			Object obj = node.getData("tag");
			if( obj instanceof String ) {
				String tag = (String)obj;
				if( !tag.equals("barrier") ) {
					continue;
				}
			} else {
				continue;
			}
			Statement IRStmt = null;
			String type = (String)node.getData("type");
			if( !type.equals("P2S") ) {
				continue;
			}
			obj = node.getData("ir");
			if( obj instanceof Statement ) {
				IRStmt = (Statement)obj;
			} else {
				continue;
			}
			if( IRStmt != null ) {
				Statement pStmt = node.getData("pKernelRegion");
				//AnalysisTools.REGIONMAP gMustDefSet = null;
				HashMap<String, String> gMustDefSet = null;
				CudaAnnotation mustDefAnnot = IRStmt.getAnnotation(CudaAnnotation.class, "mustdefset");
				if( mustDefAnnot != null ) {
					gMustDefSet = mustDefAnnot.get("mustdefset");
				} else {
					//Tools.exit("[ERROR in gLiveCVarAnalysis()] mustdefset clause is missing!");
					gMustDefSet = new HashMap<String, String>();
				}
				HashSet<String> noG2CMemTrSet = null;
				CudaAnnotation nog2cAnnot = pStmt.getAnnotation(CudaAnnotation.class, "nog2cmemtr");
				if( nog2cAnnot != null ) {
					noG2CMemTrSet = nog2cAnnot.get("nog2cmemtr");
				}
				CudaAnnotation g2cAnnot = pStmt.getAnnotation(CudaAnnotation.class, "g2cmemtr");
				HashSet<String> G2CMemTrSet = null;
				if( g2cAnnot != null ) {
					G2CMemTrSet = g2cAnnot.get("g2cmemtr");
				}
				HashSet<Symbol> gLiveCVarsSet = node.getData("gLiveCVars_out");
				HashSet<String> cudaNoG2CMemTrSet = new HashSet<String>();
				OmpAnnotation annot = pStmt.getAnnotation(OmpAnnotation.class, "parallel");
				if( annot != null ) {
					Set<Symbol> sharedVars = (Set<Symbol>)annot.get("shared");
					if( sharedVars != null ) {
						for( Symbol sym : sharedVars ) {
							List symbolInfo = AnalysisTools.findOrgSymbol(sym, pStmt);
							if( symbolInfo.size() == 2 ) {
								Symbol gSym = (Symbol)symbolInfo.get(0);
								String region = gMustDefSet.get(gSym.getSymbolName());
								if( region != null ) {
									if( region.equals("CPU") ) {
										cudaNoG2CMemTrSet.add(sym.getSymbolName());
									} else if( !gLiveCVarsSet.contains(gSym) ) {
										if( MemTrOptLevel <= 3 ) {
											if( !SymbolTools.isArray(sym) ) {
												cudaNoG2CMemTrSet.add(sym.getSymbolName());
											}
										} else {
											cudaNoG2CMemTrSet.add(sym.getSymbolName());
										}
									}
								}
							}
						}
						if( G2CMemTrSet != null ) {
							cudaNoG2CMemTrSet.removeAll(G2CMemTrSet);
						}
						if( !cudaNoG2CMemTrSet.isEmpty() ) {
							if( notClonable ) {
								if( noG2CMemTrSet != null ) {
									noG2CMemTrSet.retainAll(cudaNoG2CMemTrSet);
								}
							} else {
								if( nog2cAnnot == null ) {
									AnnotationAdded = true;
									nog2cAnnot = new CudaAnnotation("gpurun", "true");
									nog2cAnnot.put("nog2cmemtr", (HashSet<String>)cudaNoG2CMemTrSet.clone());
									pStmt.annotate(nog2cAnnot);
								} else {
									if( !noG2CMemTrSet.containsAll(cudaNoG2CMemTrSet) ) {
										AnnotationAdded = true;
										noG2CMemTrSet.addAll(cudaNoG2CMemTrSet);
									}
								}
							}
						} else if( notClonable ) {
							if( nog2cAnnot != null ) {
								nog2cAnnot.remove("nog2cmemtr");
							}
						}
					}
				}
			}
		}
		if( (clonedProc != null) && (!AnnotationAdded) ) {
			PrintTools.println("[gLiveCVarAnalysis] delete cloned procedure: " + clonedProc.getSymbolName(), 1);
			Traversable tu = clonedProc.getParent();
			tu.removeChild(clonedProc);
			newFCall.swapWith(orgFCall);
			if( !clonedProcDecls.isEmpty() ) {
				for( VariableDeclaration cProcDecl : clonedProcDecls ) {
					Traversable pTu = cProcDecl.getParent();
					TransformTools.removeChild(pTu, cProcDecl);
				}
			}
			visitedProcs2.remove(clonedProc);
		}
		
		PrintTools.println("[gLiveCVarAnalysis] analysis of " + proc.getSymbolName() + " ended", 2);
		return AnnotationAdded;
	}
}
