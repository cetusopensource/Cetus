package omp2gpu.analysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import omp2gpu.hir.CUDASpecifier;
import omp2gpu.hir.CudaAnnotation;
import omp2gpu.hir.KernelFunctionCall;
import omp2gpu.transforms.SplitOmpPRegion;

import cetus.analysis.AnalysisPass;
import cetus.analysis.CFGraph;
import cetus.analysis.CallGraph;
import cetus.analysis.DFANode;
import cetus.analysis.RangeAnalysis;
import cetus.analysis.RangeDomain;
import cetus.analysis.Section;
import cetus.exec.Driver;
import cetus.hir.Annotation;
import cetus.hir.AnnotationStatement;
import cetus.hir.Declaration;
import cetus.hir.DeclarationStatement;
import cetus.hir.DepthFirstIterator;
import cetus.hir.ExpressionStatement;
import cetus.hir.Expression;
import cetus.hir.ForLoop;
import cetus.hir.FunctionCall;
import cetus.hir.Identifier;
import cetus.hir.OmpAnnotation;
import cetus.hir.Procedure;
import cetus.hir.Program;
import cetus.hir.Statement;
import cetus.hir.Symbol;
import cetus.hir.Tools;
import cetus.hir.UnaryOperator;
import cetus.hir.UnaryExpression;
import cetus.hir.DataFlowTools;
import cetus.hir.PrintTools;
import cetus.hir.IRTools;
import cetus.hir.SymbolTools;
import cetus.hir.CompoundStatement;
import cetus.hir.Traversable;
import cetus.hir.VariableDeclarator;

public class MemTrAnalysis extends AnalysisPass {

	private int debug_level;
	private int MemTrOptLevel = 2;
	/**
	 * @param program
	 */
	public MemTrAnalysis(Program program) {
		super(program);
		debug_level = PrintTools.getVerbosity();
	}

	/* (non-Javadoc)
	 * @see cetus.analysis.AnalysisPass#getPassName()
	 */
	@Override
	public String getPassName() {
		return new String("[MemTrAnalysis]");
	}

	/* (non-Javadoc)
	 * @see cetus.analysis.AnalysisPass#start()
	 */
	@Override
	public void start() {
		String value = Driver.getOptionValue("cudaMemTrOptLevel");
		if( value != null ) {
			MemTrOptLevel = Integer.valueOf(value).intValue();
		}
		boolean assumeNonZeroTripLoops = false;
		value = Driver.getOptionValue("assumeNonZeroTripLoops");
		if( value != null ) {
			//assumeNonZeroTripLoops = Boolean.valueOf(value).booleanValue();
			assumeNonZeroTripLoops = true;
		}
		AnalysisTools.markIntervalForKernelRegions(program);
		if( MemTrOptLevel > 2 ) {
			memTrOpt2(assumeNonZeroTripLoops);
		} else {
			memTrOpt1();
		}
		
		SplitOmpPRegion.cleanExtraBarriers(program, false);
	}
	
	/**
	 * Redundant memory transfer elimination by analyzing read-only shared variables 
	 * in a kernel region; if a shared variable is read-only in a kernel region, 
	 * GPU-to-CPU memory transfer can be removed safely.
	 * 
	 */
	private void memTrOpt1() {
		/////////////////////////////////////////////////////////////////////////////////////
		//DEBUG: CallGraph.getTopologicalCallList() returns only procedures reachable from //
		// the main procedure. To access all procedures, use an iterator.                  //
		/////////////////////////////////////////////////////////////////////////////////////
/*		// generate a list of procedures in post-order traversal
		CallGraph callgraph = new CallGraph(program);
		// procedureList contains Procedure in ascending order; the last one is main
		List<Procedure> procedureList = callgraph.getTopologicalCallList();*/
		/* iterate to search for all Procedures */
		DepthFirstIterator proc_iter = new DepthFirstIterator(program);
		Set<Procedure> procedureList = (Set<Procedure>)(proc_iter.getSet(Procedure.class));

		/* drive the engine; visit every procedure */
		for (Procedure proc : procedureList)
		{
			List<FunctionCall> funcCallList = null;
			List<OmpAnnotation> bBarrier_annots = (List<OmpAnnotation>)
			IRTools.collectPragmas(proc.getBody(), OmpAnnotation.class, "barrier");
			if( bBarrier_annots.isEmpty() ) {
				continue;
			} else {
				funcCallList = IRTools.getFunctionCalls(proc.getBody());
			}
			for( OmpAnnotation omp_annot : bBarrier_annots ) {
				String type = (String)omp_annot.get("barrier");
				Statement bstmt = null;
				Statement pstmt = null;
				if( type.equals("S2P") ) {
					bstmt = (Statement)omp_annot.getAnnotatable();
					pstmt = AnalysisTools.getStatementAfter((CompoundStatement)bstmt.getParent(), 
							bstmt);
				} else {
					continue;
				}
				OmpAnnotation annot = pstmt.getAnnotation(OmpAnnotation.class, "shared");
				if( annot != null ) {
					Set<Symbol> sharedVars = annot.get("shared");
					/////////////////////////////////////////////////////////////////////////
					// accessedSymbols contains symbols accessed in a parallel region, but //
					// do not include symbols accessed only in called functions.           //
					/////////////////////////////////////////////////////////////////////////
					Set<Symbol> accessedSymbols = AnalysisTools.getAccessedVariables(pstmt);
					HashSet<String> noG2CMemTrSet = null;
					HashSet<String> cudaNoG2CMemTrSet = new HashSet<String>();
					CudaAnnotation noG2CAnnot = null;
					HashSet<String> G2CMemTrSet = new HashSet<String>();
					List<CudaAnnotation> cudaAnnots = pstmt.getAnnotations(CudaAnnotation.class);
					if( cudaAnnots != null ) {
						for( CudaAnnotation cannot : cudaAnnots ) {
							HashSet<String> dataSet = (HashSet<String>)cannot.get("nog2cmemtr");
							if( dataSet != null ) {
								//noG2CMemTrSet.addAll(dataSet);
								noG2CMemTrSet = dataSet;
								noG2CAnnot = cannot;
								//break;
							}
							dataSet = (HashSet<String>)cannot.get("g2cmemtr");
							if( dataSet != null ) {
								G2CMemTrSet.addAll(dataSet);
								//break;
							}
						}
					}
					Set<Symbol> tDefSet = DataFlowTools.getDefSymbol(pstmt);
					Set<Symbol> defSet = AnalysisTools.getBaseSymbols(tDefSet);
					for( Symbol sym: sharedVars ) {
						/////////////////////////////////////////////////////////////////////////
						// Analyses used for MemTrAnalysis are intra-procedural ones, and thus //
						// if shared variables are accessed in called functions but not in the //
						// enclosing parallel region, they will not be included in defSet;     //
						// don's defSet-based optimization to these variables.                 //
						/////////////////////////////////////////////////////////////////////////
						if( !accessedSymbols.contains(sym) ) {
							continue;
						}
						///////////////////////////////////////////////////////////////////////////
						// If shared variable is passed by reference to a function called in the //
						// current procedure, do not apply defSet-based optimization.            // 
						///////////////////////////////////////////////////////////////////////////
						boolean passedByRef = false;
						Identifier symID = new Identifier(sym);
						for( FunctionCall fCall : funcCallList ) {
							Procedure calledProc = fCall.getProcedure();
							if( calledProc == null ) {
								continue;
							}
							List<Expression> argList = (List<Expression>)fCall.getArguments();
							if( argList.isEmpty() ) {
								continue;
							}
							List paramList = calledProc.getParameters();
							int i = 0;
							for( Expression arg : argList ) {
								if( IRTools.containsSymbol(arg, sym) ) {
									List declaredSyms = ((Declaration)paramList.get(i)).getChildren();
									Symbol paramSym = (VariableDeclarator)declaredSyms.get(0);
									if( SymbolTools.isArray(paramSym) || SymbolTools.isPointer(paramSym) ) {
										if( SymbolTools.isScalar(sym) && !SymbolTools.isPointer(sym)) {
											List<UnaryExpression> uExpList = 
												IRTools.getUnaryExpression(arg, UnaryOperator.ADDRESS_OF);
											for( UnaryExpression uExp : uExpList ) {
												if( uExp.getExpression().equals(symID) ) {
													passedByRef = true;
													break;
												}
											}
											if( passedByRef ) {
												break;
											}
										} else {
											passedByRef = true;
											break;
										}
									}
								}
								i++;
							}
							if( passedByRef ) {
								break;
							}
						}
						if( passedByRef ) {
							continue;
						}
						if( !defSet.contains(sym) ) {
							String symName = sym.getSymbolName();
							if( !G2CMemTrSet.contains(symName) ) {
								//no memory transfer is needed!
								cudaNoG2CMemTrSet.add(symName);
							}
						}
					}
					if( cudaNoG2CMemTrSet.size() > 0 ) {
						if( noG2CAnnot == null ) {
							noG2CAnnot = new CudaAnnotation("gpurun", "true");
							noG2CAnnot.put("nog2cmemtr", cudaNoG2CMemTrSet);
							pstmt.annotate(noG2CAnnot);
						} else {
							noG2CMemTrSet.addAll(cudaNoG2CMemTrSet);
						}
					}
				}
			}
		}
	}
	
	/**
	 * Redundant memory transfer elimination by analyzing upwardly exposed shared
	 * variables (UESV); if the reaching definition of the UESV is from the same 
	 * region. (i.e., the reaching definition of a UESV in a kernel region is from
	 * a previous kernel region, we don't have to insert CPU-to-GPU memory transfer.)  
	 * This analysis is unsafe; refer to the known bugs shown below.
	 * <p>
	 * FIXME: 1) This analysis uses array-name-only analysis, and thus if a shared 
	 * array is partially written and other part of the array is read later, this 
	 * analysis still considers that there is no upward exposed use. 
	 * 2) If a shared variable is accessed only by a GPU in a function, but accessed by a CPU 
	 * after the function returns, this analysis fails to add a necessary GPU-to-CPU memory 
	 * transfer call. (Even if the shared variable is accessed only by a GPU after the function
	 * returns, the analysis may insert incorrect CPU-to-GPU memory transfer call.)
	 * To fix this problem, all modified shared variables are flushed back to CPU, but because
	 * this flush relies on AnalysisTools.liveGVariableAnalysis(), which is a MAY analysis, 
	 * this flush may not cover all necessary flush operations.
	 * 3) This analysis can not handle function calls if other kernel regions exist in the called
	 * function, but shared variables are not passed as function arguments.
	 * 4) The following code pattern will not work correctly:
	 *     kernelcall1(); //where shared variable A is modified.
	 *     for ( ... ) {
	 *         kernelcall2(); //where shared variable A is accessed.
	 *         A = ...; //A is modified by CPU.
	 *     }
	 * - In the above code, kernelcall1 does not transfer A back to CPU, since it knows that
	 *   A is accessed by the following kernelcall2. However, kernelcall2 will transfer A
	 *   from CPU, since the modification of A by CPU is reachable to the kernelcall2.    
	 *     
	 */
	private void memTrOpt2(boolean assumeNonZeroTripLoops) {
		/////////////////////////////////////////////////////////////////////////////////////
		//DEBUG: CallGraph.getTopologicalCallList() returns only procedures reachable from //
		// the main procedure. To access all procedures, use an iterator.                  //
		/////////////////////////////////////////////////////////////////////////////////////
/*		// generate a list of procedures in post-order traversal
		CallGraph callgraph = new CallGraph(program);
		// procedureList contains Procedure in ascending order; the last one is main
		List<Procedure> procedureList = callgraph.getTopologicalCallList();*/
		/* iterate to search for all Procedures */
		DepthFirstIterator proc_iter = new DepthFirstIterator(program);
		Set<Procedure> procedureList = (Set<Procedure>)(proc_iter.getSet(Procedure.class));
		HashSet<Procedure> visitedProcedures = new HashSet<Procedure>();

		///////////////////////
		// DEBUG: deprecated //
		///////////////////////
		//RangeAnalysis range = new RangeAnalysis(program);

		/* drive the engine; visit every procedure */
		for (Procedure proc : procedureList)
		{
			/////////////////////////////////////////////
			// This analysis is conducted on functions // 
			// containing omp parallel region.         //
			/////////////////////////////////////////////
			List<OmpAnnotation> pRegion_annots = (List<OmpAnnotation>)
			IRTools.collectPragmas(proc.getBody(), OmpAnnotation.class, "parallel");
			if( pRegion_annots.size() == 0 ) {
				//DEBUG orignally 2.
				PrintTools.println("The procedure, " + proc.getName() + ", is skipped.", 2);
				continue;
			} else if( visitedProcedures.contains(proc) ) {
				continue;
			}
			visitedProcedures.add(proc);
			PrintTools.println("Procedure name: "+ proc.getName(), 1);

			// Find a set of shared variables in the kernel function.
			Set<Symbol> shared_vars = AnalysisTools.getOmpSharedVariables(proc);
			PrintTools.print("Shared variable symbols in a fucntion " + proc.getName() + " = ", 5);
			PrintTools.println("{" + PrintTools.collectionToString(shared_vars, ",") + "}", 5);
			
			List<FunctionCall> funcCallList = IRTools.getFunctionCalls(proc.getBody());

			// Set of GPU variables that are written in kernels but not flushed back to a CPU.
			Set<Symbol> gModOnlySet = new HashSet<Symbol>();
			// HashMap of (kernel region, advLiveG_in set)
			//HashMap<Statement, Set<Symbol>> advLiveGInMap = new HashMap<Statement, Set<Symbol>>();

			// get the range map
			// RangeAnalysis is not needed LiveAnalysis0 and ReachAnalysis0.
			//Map<Statement, RangeDomain> rmap = RangeAnalysis.getRanges(proc);

			OCFGraph.setNonZeroTripLoops(assumeNonZeroTripLoops);
			CFGraph cfg = new OCFGraph(proc, null);

			// sort the control flow graph
			cfg.topologicalSort(cfg.getNodeWith("stmt", "ENTRY"));

			// attach the range information to the control flow graph
			//AnalysisTools.addRangeDomainToCFG(cfg, rmap);

			// perform reaching-definition analysis (It should come before LiveAnalysis)
			ReachAnalysis0 reach_analysis = new ReachAnalysis0(proc, cfg, shared_vars);
			reach_analysis.run();

			// perform live-out analysis (It should come after ReachAnalysis)
			LiveAnalysis0 live_analysis = new LiveAnalysis0(proc, cfg, shared_vars, true);
			live_analysis.run();

			// Backward data-flow analysis to compute liveG_out, a set of live GPU variables, 
			// which are accessed in later nodes. 
			AnalysisTools.annotateBarriers(proc, cfg);
			AnalysisTools.liveGVariableAnalysis(cfg, false);
			AnalysisTools.reachingGMallocAnalysis(cfg);
			AnalysisTools.advLiveGVariableAnalysis(cfg, false);
			
			//if( MemTrOptLevel > 3) {
				// Analyses needed for residentGVariableAnalysis().
				AnalysisTools.cudaMallocFreeAnalsys(cfg);
				// Resident GPU variable analysis
				AnalysisTools.residentGVariableAnalysis(cfg);
			//}

			//Section.MAP ueuse = null;

			PrintTools.println("Number of cetus parallel annotations in this procedure: "
					+ pRegion_annots.size() , 3);
			HashSet<Statement> bBarriers = new HashSet<Statement>();
			HashMap<Statement, Statement> pRegions = new HashMap<Statement, Statement>();
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
					bBarriers.add(bstmt);
					pRegions.put(bstmt, pstmt);
				} else if( type.equals("P2S") ) {
					bstmt = (Statement)omp_annot.getAnnotatable();
					pstmt = AnalysisTools.getStatementBefore((CompoundStatement)bstmt.getParent(), 
							bstmt);
					bBarriers.add(bstmt);
					pRegions.put(bstmt, pstmt);
				} else {
					continue;
				}
			}

			// cfg.iterator() does not guarantee sorted visiting,
			// even though it seems to work.
			// For safety, we use sorted work_list instead.
			/*			Iterator<DFANode> iter = cfg.iterator();
			while ( iter.hasNext() )
			{
				DFANode node = iter.next();*/
			TreeMap work_list = new TreeMap();
			// Visited Node Set to prevent infinite loops.
			HashSet<DFANode> visitedNodes = new HashSet<DFANode>();
			// Enter the entry node in the work_list
			DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
			work_list.put(entry.getData("top-order"), entry);

			// Do iterative steps
			while ( !work_list.isEmpty() )
			{
				DFANode node = (DFANode)work_list.remove(work_list.firstKey());
				for ( DFANode succ : node.getSuccs() ) {
					if( !visitedNodes.contains(succ) ) {
						visitedNodes.add(succ);
						work_list.put(succ.getData("top-order"), succ);
					}
				}
				if( bBarriers.size() == 0 ) {
					// All parallel regions of interest are searched.
					break;
				}
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
				obj = node.getData("ir");
				if( obj instanceof Statement ) {
					IRStmt = (Statement)obj;
				} else {
					continue;
				}

				boolean found_bBarrier = false;
				Statement foundStmt = null;
				for( Statement stmt : bBarriers ) {
					if( stmt.equals(IRStmt) ) {
						found_bBarrier = true;
						foundStmt = stmt;
						break;
					}
				}
				if( found_bBarrier ) {
					// At a barrier ueuse is reset, and thus get data 
					// from live_out set.
					//ueuse = (Section.MAP)node.getData("live_out");
					Statement pStmt = pRegions.get(foundStmt);
					OmpAnnotation annot = pStmt.getAnnotation(OmpAnnotation.class, "shared");
					if( annot != null ) {
						Set<Symbol> sharedVars = annot.get("shared");
						/////////////////////////////////////////////////////////////////////////
						// accessedSymbols contains symbols accessed in a parallel region, but //
						// do not include symbols accessed only in called functions.           //
						/////////////////////////////////////////////////////////////////////////
						Set<Symbol> accessedSymbols = AnalysisTools.getAccessedVariables(pStmt);
						//Set<Symbol> ueuseVars = ueuse.keySet();
						Set<Symbol> ueuseVars = (Set<Symbol>)node.getData("live_out");
						String type = (String)node.getData("type");
						AnalysisTools.REGIONMAP must_def_outRM = 
							(AnalysisTools.REGIONMAP)node.getData("must_def_outRM");
						if( must_def_outRM == null ) {
							must_def_outRM = new AnalysisTools.REGIONMAP();
						}
						HashSet<String> noC2GMemTrSet = null;
						HashSet<String> noG2CMemTrSet = null;
						HashSet<String> MultiSrcCGSet = null;
						HashSet<String> ConditionalSrcSet = null;
						HashSet<String> C2GMemTrSet = new HashSet<String>();
						HashSet<String> G2CMemTrSet = new HashSet<String>();
						HashSet<String> cudaNoC2GMemTrSet = new HashSet<String>();
						HashSet<String> cudaNoG2CMemTrSet = new HashSet<String>();
						HashSet<String> cudaMultiSrcCGSet = new HashSet<String>();
						HashSet<String> cudaConditionalSrcSet = new HashSet<String>();
						CudaAnnotation noC2GAnnot = null;
						CudaAnnotation noG2CAnnot = null;
						CudaAnnotation multipleAnnot = null;
						CudaAnnotation conditionalAnnot = null;
						List<CudaAnnotation> cudaAnnots = pStmt.getAnnotations(CudaAnnotation.class);
						if( cudaAnnots != null ) {
							for( CudaAnnotation cannot : cudaAnnots ) {
								HashSet<String> dataSet = (HashSet<String>)cannot.get("noc2gmemtr");
								if( dataSet != null ) {
									noC2GMemTrSet = dataSet;
									noC2GAnnot = cannot;
								}
								dataSet = (HashSet<String>)cannot.get("nog2cmemtr");
								if( dataSet != null ) {
									//noG2CMemTrSet.addAll(dataSet);
									noG2CMemTrSet = dataSet;
									noG2CAnnot = cannot;
								}
								dataSet = (HashSet<String>)cannot.get("c2gmemtr");
								if( dataSet != null ) {
									C2GMemTrSet.addAll(dataSet);
								}
								dataSet = (HashSet<String>)cannot.get("g2cmemtr");
								if( dataSet != null ) {
									G2CMemTrSet.addAll(dataSet);
								}
								dataSet = (HashSet<String>)cannot.get("multisrccg");
								if( dataSet != null ) {
									MultiSrcCGSet = dataSet;
									multipleAnnot = cannot;
								}
								dataSet = (HashSet<String>)cannot.get("conditionalsrc");
								if( dataSet != null ) {
									ConditionalSrcSet = dataSet;
									conditionalAnnot = cannot;
								}
							}
						}
						if( type.equals("S2P") ) {
							//Set<Symbol> advLiveG_in = node.getData("advLiveG_in");
							//if( advLiveG_in == null ) {
							//	PrintTools.println("==> Error in Parallel region: \n"+ pStmt, 1);
							//	Tools.exit("[Error in memTrOpt2()] advLiveG_in set does not exist");
							//}
							//advLiveGInMap.put(pStmt, advLiveG_in);
							Set<Symbol> reachingGMalloc_in = node.getData("reachingGMalloc_in");
							if( reachingGMalloc_in == null ) {
								PrintTools.println("==> Error in Parallel region: \n"+ pStmt, 1);
								Tools.exit("[Error in memTrOpt2()] reachingGMalloc_in set does not exist");
							}
							Set<Symbol> residentG_out = null;
							//if( MemTrOptLevel > 3 ) {
								residentG_out = node.getData("residentGVars_out");
								if( residentG_out == null ) {
									PrintTools.println("==> Error in Parallel region: \n"+ pStmt, 1);
									Tools.exit("[Error in memTrOpt2()] residentGVars_out set does not exist");
								}
							//}
							for( Symbol sym: sharedVars ) {
								/////////////////////////////////////////////////////////////////////////
								// Analyses used for MemTrAnalysis are intra-procedural ones, and thus //
								// if shared variables are accessed in called functions but not in the //
								// enclosing parallel region, they will not be included in ueuseVars   //
								// set; don't apply ueuse-based optimization to these variables.       //
								/////////////////////////////////////////////////////////////////////////
								if( !accessedSymbols.contains(sym) ) {
									continue;
								}
								///////////////////////////////////////////////////////////////////////////
								// If shared variable is passed by reference to a function called in the //
								// current procedure, do not apply ueuse-based optimization.             // 
								///////////////////////////////////////////////////////////////////////////
								boolean passedByRef = false;
								Identifier symID = new Identifier(sym);
								for( FunctionCall fCall : funcCallList ) {
									Procedure calledProc = fCall.getProcedure();
									if( calledProc == null ) {
										continue;
									}
									List<Expression> argList = (List<Expression>)fCall.getArguments();
									if( argList.isEmpty() ) {
										continue;
									}
									List paramList = calledProc.getParameters();
									int i = 0;
									for( Expression arg : argList ) {
										if( IRTools.containsSymbol(arg, sym) ) {
											List declaredSyms = ((Declaration)paramList.get(i)).getChildren();
											Symbol paramSym = (VariableDeclarator)declaredSyms.get(0);
											if( SymbolTools.isArray(paramSym) || SymbolTools.isPointer(paramSym) ) {
												if( SymbolTools.isScalar(sym) && !SymbolTools.isPointer(sym)) {
													List<UnaryExpression> uExpList = 
														IRTools.getUnaryExpression(arg, UnaryOperator.ADDRESS_OF);
													for( UnaryExpression uExp : uExpList ) {
														if( uExp.getExpression().equals(symID) ) {
															passedByRef = true;
															break;
														}
													}
													if( passedByRef ) {
														break;
													}
												} else {
													passedByRef = true;
													break;
												}
											}
										}
										i++;
									}
									if( passedByRef ) {
										break;
									}
								}
								if( passedByRef ) {
									continue;
								}
								String symName = sym.getSymbolName();
								if( ueuseVars.contains(sym) ) {
									String region = must_def_outRM.get(sym);
									if( region == null ) {
										/////////////////////////////////////////////////////////////////////////////
										// This analysis is not sure whether this symbol is written in GPU or not. //
										/////////////////////////////////////////////////////////////////////////////
										if( residentG_out.contains(sym) ) {
											// But GPU global memory has a copy of it.
											// No memory transfer is needed.
											if( !C2GMemTrSet.contains(symName) ) {
												if( MemTrOptLevel <= 3 ) {
													////////////////////////////////////////////////////////////
													//Current implementation uses array-name-only analysis,   //
													//which can be incorrect, and thus if MemTrOptLevel == 3, // 
													//conservatively move array variable from CPU to GPU.     //
													////////////////////////////////////////////////////////////
													if( !SymbolTools.isArray(sym) ) {
														cudaNoC2GMemTrSet.add(symName);
													}
												} else {
													cudaNoC2GMemTrSet.add(symName);
												}
											}
										}
									} else if( region.equals("GPU") 
											&& reachingGMalloc_in.contains(sym) ) {
										// The symbol is modified by GPU.
										// No memory transfer is needed!
										if( !C2GMemTrSet.contains(symName) ) {
											if( MemTrOptLevel <= 3 ) {
												////////////////////////////////////////////////////////////
												//Current implementation uses array-name-only analysis,   //
												//which can be incorrect, and thus if MemTrOptLevel == 3, // 
												//conservatively move array variable from CPU to GPU.     //
												////////////////////////////////////////////////////////////
												if( !SymbolTools.isArray(sym) ) {
													cudaNoC2GMemTrSet.add(symName);
												}
											} else {
												cudaNoC2GMemTrSet.add(symName);
											}
										}
									//} else if( (MemTrOptLevel > 3) && residentG_out.contains(sym) ) {
									} else if( residentG_out.contains(sym) ) {
										// The symbol seems to be modified by CPU, but 
										// GPU global memory has a copy of it.
										// No memory transfer is needed.
										if( !C2GMemTrSet.contains(symName) ) {
											if( MemTrOptLevel <= 3 ) {
												////////////////////////////////////////////////////////////
												//Current implementation uses array-name-only analysis,   //
												//which can be incorrect, and thus if MemTrOptLevel == 3, // 
												//conservatively move array variable from CPU to GPU.     //
												////////////////////////////////////////////////////////////
												if( !SymbolTools.isArray(sym) ) {
													cudaNoC2GMemTrSet.add(symName);
												}
											} else {
												cudaNoC2GMemTrSet.add(symName);
											}
										}
									} else if( region.equals("CPUGPU") ) {
										//////////////////////////////////////////////////////////////////////
										//FIXME: Can we apply multisrccg clause even if MemTrOptLevel == 3? //
										//       Let's try this.                                            //
										//////////////////////////////////////////////////////////////////////
/*										if( MemTrOptLevel <= 3 ) {
											if( !SymbolTools.isArray(sym) ) {
												cudaMultiSrcCGSet.add(symName);
											}
										} else {
											cudaMultiSrcCGSet.add(symName);
										}*/
										cudaMultiSrcCGSet.add(symName);
									} else if( region.equals("conditional") ) {
										cudaConditionalSrcSet.add(symName);
									} else if( region.equals("Unknown") ) {
										//DEBUG
										PrintTools.println("[WARNING in MemTrAnalysis()] The region where the Symbol, " + symName 
												+ ", is defined is unknown.", 3);
									}
								} else {
									//no memory transfer is needed!
									if( !C2GMemTrSet.contains(symName) ) {
										if( MemTrOptLevel <= 3 ) {
											////////////////////////////////////////////////////////////
											//Current implementation uses array-name-only analysis,   //
											//which can be incorrect, and thus if MemTrOptLevel == 3, // 
											//conservatively move array variable from CPU to GPU.     //
											////////////////////////////////////////////////////////////
											if( !SymbolTools.isArray(sym) ) {
												cudaNoC2GMemTrSet.add(symName);
											}
										} else {
											cudaNoC2GMemTrSet.add(symName);
										}
									}
								}
							}
						} else if( type.equals("P2S") ) {
							Set<Symbol> tDefSet = DataFlowTools.getDefSymbol(pStmt);
							Set<Symbol> defSet = AnalysisTools.getBaseSymbols(tDefSet);
							//Set<Symbol> advLiveG_in = (Set<Symbol>)advLiveGInMap.remove(pStmt);
							//if( advLiveG_in == null ) {
							//	Tools.exit("[Error in memTrOpt2()] advLiveG_in set does not exist.");
							//}
							Set<Symbol> advLiveG_out = node.getData("advLiveG_out");
							if( advLiveG_out == null ) {
								PrintTools.println("==> Error in Parallel region: \n"+ pStmt, 1);
								Tools.exit("[Error in memTrOpt2()] advLiveG_out set does not exist");
							}
							for( Symbol sym: sharedVars ) {
								/////////////////////////////////////////////////////////////////////////
								// Analyses used for MemTrAnalysis are intra-procedural ones, and thus //
								// if shared variables are accessed in called functions but not in the //
								// enclosing parallel region, they will not be included in defSet;     //
								// don's defSet-based optimization to these variables.                 //
								/////////////////////////////////////////////////////////////////////////
								if( !accessedSymbols.contains(sym) ) {
									continue;
								}
								///////////////////////////////////////////////////////////////////////////
								// If shared variable is passed by reference to a function called in the //
								// current procedure, do not apply defSet-based optimization.            // 
								///////////////////////////////////////////////////////////////////////////
								boolean passedByRef = false;
								Identifier symID = new Identifier(sym);
								for( FunctionCall fCall : funcCallList ) {
									Procedure calledProc = fCall.getProcedure();
									if( calledProc == null ) {
										continue;
									}
									List<Expression> argList = (List<Expression>)fCall.getArguments();
									if( argList.isEmpty() ) {
										continue;
									}
									List paramList = calledProc.getParameters();
									int i = 0;
									for( Expression arg : argList ) {
										if( IRTools.containsSymbol(arg, sym) ) {
											List declaredSyms = ((Declaration)paramList.get(i)).getChildren();
											Symbol paramSym = (VariableDeclarator)declaredSyms.get(0);
											if( SymbolTools.isArray(paramSym) || SymbolTools.isPointer(paramSym) ) {
												if( SymbolTools.isScalar(sym) && !SymbolTools.isPointer(sym)) {
													List<UnaryExpression> uExpList = 
														IRTools.getUnaryExpression(arg, UnaryOperator.ADDRESS_OF);
													for( UnaryExpression uExp : uExpList ) {
														if( uExp.getExpression().equals(symID) ) {
															passedByRef = true;
															break;
														}
													}
													if( passedByRef ) {
														break;
													}
												} else {
													passedByRef = true;
													break;
												}
											}
										}
										i++;
									}
									if( passedByRef ) {
										break;
									}
								}
								if( passedByRef ) {
									continue;
								}
								String symName = sym.getSymbolName();
								if( !defSet.contains(sym) ) {
									if( advLiveG_out.contains(sym) ) {
										//no memory transfer is needed!
										if( !G2CMemTrSet.contains(symName) ) {
											cudaNoG2CMemTrSet.add(symName);
										}
									} else if (!gModOnlySet.remove(sym)) {
										//no memory transfer is needed!
										if( !G2CMemTrSet.contains(symName) ) {
											cudaNoG2CMemTrSet.add(symName);
										}
									}
								} else {
									if( ueuseVars.contains(sym) ) {
										String region = must_def_outRM.get(sym);
										//DEBUG: below is unreachable code.
										if( (region != null) && region.equals("CPU") ) {
											//no memory transfer is needed!
											if( !G2CMemTrSet.contains(symName) ) {
												if( MemTrOptLevel <= 3 ) {
													////////////////////////////////////////////////////////////
													//Current implementation uses array-name-only analysis,   //
													//which can be incorrect, and thus if MemTrOptLevel == 3, // 
													//conservatively move array variable from CPU to GPU.     //
													////////////////////////////////////////////////////////////
													if( !SymbolTools.isArray(sym) ) {
														cudaNoG2CMemTrSet.add(symName);
													}
												} else {
													cudaNoG2CMemTrSet.add(symName);
												}
											}
										}
									} else {
										// If GPU variable is modified in this kernel region 
										// but accessed in any later kernel regions, do not 
										// transfer at this kernel, memory transfer will be
										// handled by the the last kernel that accessed the 
										// variable.
										if( advLiveG_out.contains(sym) ) {
											//no memory transfer is needed!
											if( !G2CMemTrSet.contains(symName) ) {
												if( MemTrOptLevel <= 3 ) {
													////////////////////////////////////////////////////////////
													//Current implementation uses array-name-only analysis,   //
													//which can be incorrect, and thus if MemTrOptLevel == 3, // 
													//conservatively move array variable from CPU to GPU.     //
													////////////////////////////////////////////////////////////
													if( !SymbolTools.isArray(sym) ) {
														cudaNoG2CMemTrSet.add(symName);
														// This GPU variable is written in this kernel 
														// but not flushed back to a CPU.
														gModOnlySet.add(sym);
													}
												} else {
													cudaNoG2CMemTrSet.add(symName);
													// This GPU variable is written in this kernel 
													// but not flushed back to a CPU.
													gModOnlySet.add(sym);
												}
											}
										} 
									}
								}
							}
						}
						if( cudaNoC2GMemTrSet.size() > 0 ) {
							if( noC2GAnnot == null ) {
								noC2GAnnot = new CudaAnnotation("gpurun", "true");
								noC2GAnnot.put("noc2gmemtr", cudaNoC2GMemTrSet);
								pStmt.annotate(noC2GAnnot);
							} else {
								noC2GMemTrSet.addAll(cudaNoC2GMemTrSet);
							}
						}
						if( cudaNoG2CMemTrSet.size() > 0 ) {
							if( noG2CAnnot == null ) {
								noG2CAnnot = new CudaAnnotation("gpurun", "true");
								noG2CAnnot.put("nog2cmemtr", cudaNoG2CMemTrSet);
								pStmt.annotate(noG2CAnnot);
							} else {
								noG2CMemTrSet.addAll(cudaNoG2CMemTrSet);
							}
						}
						if( cudaMultiSrcCGSet.size() > 0 ) {
							if( multipleAnnot == null ) {
								multipleAnnot = new CudaAnnotation("gpurun", "true");
								multipleAnnot.put("multisrccg", cudaMultiSrcCGSet);
								pStmt.annotate(multipleAnnot);
							} else {
								MultiSrcCGSet.addAll(cudaMultiSrcCGSet);
							}
						}
						if( cudaConditionalSrcSet.size() > 0 ) {
							if( conditionalAnnot == null ) {
								conditionalAnnot = new CudaAnnotation("gpurun", "true");
								conditionalAnnot.put("conditionalsrc", cudaConditionalSrcSet);
								pStmt.annotate(conditionalAnnot);
							} else {
								ConditionalSrcSet.addAll(cudaConditionalSrcSet);
							}
						}
					}
					bBarriers.remove(foundStmt);
					pRegions.remove(foundStmt);
				}
			}

			AnalysisTools.displayCFG(cfg, debug_level);
		}
	}
}
