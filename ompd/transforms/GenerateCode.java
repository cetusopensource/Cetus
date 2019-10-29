package ompd.transforms; 

import static cetus.hir.PrintTools.println;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.HashSet;
import java.util.TreeMap;
import java.util.Map;
import java.util.HashMap;

import ompd.hir.*;
import ompd.hir.SectionSet.*;
import cetus.analysis.DFANode;
import cetus.analysis.LoopTools;
import cetus.analysis.RangeDomain;
import ompd.analysis.PCFGraph;
import ompd.analysis.OMPDReductionAnalysis;
import ompd.hir.OmpdAnnotation;
import cetus.exec.Driver;
import cetus.hir.*;

public class GenerateCode {
	
	private Program program;
	private Procedure mainProc;
	private ProgramRecord prog_record;
	private TranslationUnit globals;
	private int loopId;
	private Set<Symbol> InitializedSymbols; //set of symbols that are already passed to the runtime 
	//private Set<Integer> non_repetitive_loops; // keep track of loop IDs that have non-repetitive iteration spaces
	private DFANode last_barrier_with_non_empty_comm; // keep track of the last barrier with non_empty communication
	
	//private Symbol procid_symbol, nprocs_symbol, loop_i_symbol;

    public GenerateCode(ProgramRecord rcd){
    	this.prog_record = rcd;
    	this.mainProc = prog_record.get_main();
    	this.program = prog_record.get_program();
    	this.globals = prog_record.get_globalsTU();
    	//this.procid_symbol = prog_record.get_procid();
    	//this.loop_i_symbol = prog_record.get_loop_i();
    	//this.nprocs_symbol = prog_record.get_nprocs();
    	//this.non_repetitive_loops = new HashSet<Integer>();
    	this.loopId=0;
    }
    
    public void start() {
    	 tagLoopsInProgram(); // give loops unique numbers (loops with similar iteration spaces have same number)
    	 printSECTIONsInProgram(); // for each barrier, insert comments to show the user DEFs and USEs
    	 
    	 //omp-to-mpi translated code 
    		 if(Driver.getOptionValue("no-global-use")==null && Driver.getOptionValue("no-communication")==null) // if no global USE -- no communication
    		 	 performCommunicationInProgram(); // for each barrier, 1. pass DEFs nad USEs, 2. invoke communication
    		 performReductionAnalysis(); 
        	 partitionLoopsInProgram(); // for each loop, 1. replace bounds with {lb,ub} variables, 2. insert code to compute these {lb,ub}'s

    	 
    	 finialize();
    }
    
    private void tagLoopsInProgram(){
		for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	tagLoopsInProcedure(tu,proc);
            }
        }
	}
    private void partitionLoopsInProgram(){
		for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	partitionLoopsInProcedure(tu,proc);
            }
        }
	}
    private void printSECTIONsInProgram(){
    	for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	printSECTIONsInProcedure(tu,proc);
            }
        }
    }
    private void performCommunicationInProgram(){
    	for (TranslationUnit tu : prog_record.get_TUs()) {
    		
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	InitializedSymbols = new HashSet<Symbol>();
            	last_barrier_with_non_empty_comm = null;
            	performCommunicationInProcedure(tu,proc);
            	Initialize_Symbols(proc.getBody());
                InitializedSymbols = null;
            }
            
        }
    }
 
    private void partitionLoopsInProcedure(TranslationUnit tu, Procedure proc) {
        Set<OmpdAnnotation> annotationList = prog_record.get_loop_annot_keys(tu, proc);
        Set<Integer> finishedLoops = new HashSet<Integer>(); //keeps track of loop Ids that their bounds already computed
        for (OmpdAnnotation annotation : annotationList) {
        	insertBoundVariables(tu,proc, prog_record.get_loop_record(tu, proc, annotation),finishedLoops);
        }
    }    
    private void performReductionAnalysis(){
    	OMPDReductionAnalysis reduction_analysis = new OMPDReductionAnalysis(prog_record);
    	 for (TranslationUnit tu : prog_record.get_TUs()) {
	            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
	            	reduction_analysis.start(tu, proc);
	            }
	        }
    }
    
    private void tagLoopsInProcedure(TranslationUnit tu, Procedure proc) {
    	
    	Set<OmpdAnnotation> annotationList = prog_record.get_loop_annot_keys(tu, proc);
        for (OmpdAnnotation annotation : annotationList) {
        	tagLoop(tu,proc,prog_record.get_loop_record(tu, proc, annotation));
        }
    }
    private void tagLoop(TranslationUnit tu, Procedure proc, OMPDParallelForLoop pfor){
    	Expression orig_lb = pfor.get_orig_lb();
    	Expression orig_ub = pfor.get_orig_ub();
    	Expression orig_step = pfor.get_step();
    	
    	// find out if bounds of a prior loop with a similar iteration space was partitioned
    	int x;
    	if(!pfor.IsRepetitive())
    		x = prog_record.get_bound_record(tu, proc).getLoopId(pfor.get_outer_serial_loop().getBody(), orig_lb, orig_ub, orig_step);
    	else
    		x = prog_record.get_bound_record(tu, proc).getLoopId(orig_lb, orig_ub, orig_step);

        if(x==-1){ // bounds were never computed before
        	//declare Bound Variables
        	NameID pi_id = new NameID("ompd_pi" + loopId);
            VariableDeclarator pi_declarator = new VariableDeclarator(PointerSpecifier.UNQUALIFIED, pi_id);
        	Declaration pi_decl = new VariableDeclaration(new UserSpecifier(new NameID("pi_struct")), pi_declarator);
        	if(!pfor.IsRepetitive()){
        		((CompoundStatement)pfor.get_outer_serial_loop().getBody()).addDeclaration(pi_decl);
        		((CompoundStatement)pfor.get_outer_serial_loop().getBody()).addStatement(ompd_discard_partition(pi_id.clone()));
        	}
        	else
        		globals.addDeclarationFirst(pi_decl);
        	
        	//mark "bounds are computed" for future loops with similar iteration spaces
        	if(!pfor.IsRepetitive())
        		prog_record.get_bound_record(tu, proc).add(loopId, pfor.get_outer_serial_loop().getBody(), orig_lb, orig_ub, orig_step);
        	else
        		prog_record.get_bound_record(tu, proc).add(loopId, orig_lb, orig_ub, orig_step);
            pfor.set_loopId(loopId);
            loopId++; 
        }
        else // bounds were already computed by a prior loop
        	pfor.set_loopId(x);
    }

    private void insertBoundVariables(TranslationUnit tu, Procedure proc, OMPDParallelForLoop pfor, Set<Integer> finishedLoops) {

    	int ID = pfor.get_loopId();
    	
        
      //replace Bounds in loop
        VariableDeclarator lb_declarator = new VariableDeclarator(new NameID("ompd_pi" + ID +"->lb"));
        VariableDeclarator ub_declarator = new VariableDeclarator(new NameID("ompd_pi" + ID +"->ub"));
        ForLoop loop = pfor.get_Forloop();
        ExpressionStatement init_stmt = (ExpressionStatement) loop.getInitialStatement();
        Expression init_rhse = ((BinaryExpression) init_stmt.getExpression()).getRHS();
        init_rhse.swapWith(new Identifier (lb_declarator));
        BinaryExpression new_cond_expr;
        /*fix this based on stride direction*/
         BinaryExpression cond = (BinaryExpression)loop.getCondition();
         if(cond.getOperator() == BinaryOperator.COMPARE_LE || cond.getOperator() == BinaryOperator.COMPARE_LT){
        	 new_cond_expr = new BinaryExpression(LoopTools.getIndexVariable(loop).clone(),
                     BinaryOperator.COMPARE_LE, new Identifier (ub_declarator) );
        	 loop.setCondition(new_cond_expr);
         }
         else if(cond.getOperator() == BinaryOperator.COMPARE_GE || cond.getOperator() == BinaryOperator.COMPARE_GT){
        	 new_cond_expr = new BinaryExpression(LoopTools.getIndexVariable(loop).clone(),
                     BinaryOperator.COMPARE_GE, new Identifier (ub_declarator) );
        	 loop.setCondition(new_cond_expr);
         }
         else
        	 Tools.exit("ERROR in insertBoundVariables: Unsupported loop condition expression");
         
         
       
    	
        if(!finishedLoops.contains(ID)){// bounds were never computed before -- insert 
            //insert partitioning code 
        	
        	//find accessed symbols in iteration space variables
        	Expression orig_lb = pfor.get_orig_lb();
        	Expression orig_ub = pfor.get_orig_ub();
        	Expression orig_step = pfor.get_step();
        	Set<Symbol> useSymbols = new HashSet<Symbol>(); // all accessed symbols in 
            useSymbols.addAll(DataFlowTools.getUseSymbol(orig_lb));
            useSymbols.addAll(DataFlowTools.getUseSymbol(orig_ub));
            useSymbols.addAll(DataFlowTools.getUseSymbol(orig_step));
            
          // library calls to compute lb,ub and blk
            CompoundStatement cs = new CompoundStatement();
        	NameID pi_id = new NameID("ompd_pi" + ID);
            VariableDeclarator pi_declarator = new VariableDeclarator(pi_id);
            cs.addStatement(ompd_partition(orig_lb,orig_ub,orig_step,new Identifier(pi_declarator)));
            if(Driver.getOptionValue("print-bounds")!=null)
            	cs.addStatement(ompd_print_bounds(ID,new Identifier (pi_declarator)));
            
            // insert partitioning code 
            insert_statements_AsEarlyAsPossible(cs,(Statement) pfor.get_Forloop(),useSymbols,proc);
            
            finishedLoops.add(ID); // mark this iteration space as "finished" for future loops with similar iteration spaces
        }
    }
    
 SectionSet.MAP substituteInfiniteSections(SectionSet.MAP set, Set<Symbol> commonSymbols, RangeDomain rd) {
	 if(set==null || set.isEmpty())
		 return set;
	 SectionSet.MAP USEGlobal = set.clone();
	 for(Symbol s: commonSymbols){
		 boolean foundInfinite = false;
		 SectionSet USEs = new SectionSet();
		 SectionSet delete = new SectionSet();
		 for(SECTION sec: USEGlobal.get(s)){
			 if(sec.isRSD() && ((RSD)sec).containsInfiniteElement()){
				 RSD tmp = (RSD)sec.clone();
				 tmp.replaceInfiniteElements();
				 delete.add(sec);
				 USEs.add(tmp,rd);
				 foundInfinite = true;
			 }
			 else if(sec.isERSD() && ((ERSD)sec).get(0).containsInfiniteElement()){
				 RSD tmp = ((ERSD)sec).get(0).clone();
				 tmp.replaceInfiniteElements();
				 delete.add(sec);
				 SectionSet right_terms = new SectionSet();
				 for(int i=1;i<((ERSD)sec).size();i++)
			    		right_terms.add(((ERSD)sec).get(i));
				 USEs=USEs.unionWith(SectionSet.subtractSetFromSection(tmp, right_terms, rd), rd);
				 foundInfinite = true;
			 }
		 }
		 if(foundInfinite){
			 for(SECTION sec:delete)
				 USEGlobal.get(s).remove(sec);
			 for(SECTION sec:USEs)
				 USEGlobal.get(s).add(sec, rd);
		 }
	 } 
	 return USEGlobal;
 }
 SectionSet.MAP substituteInfiniteSections_xp(SectionSet.MAP set, Set<Symbol> commonSymbols, RangeDomain rd) {
	 if(set==null || set.isEmpty())
		 return set;
	 SectionSet.MAP USEGlobal = set.clone();
	 for(Symbol s: commonSymbols){
		 boolean foundInfinite = false;
		 SectionSet USEs = new SectionSet();
		 SectionSet delete = new SectionSet();
		 for(SECTION sec: USEGlobal.get(s)){
			 if(sec.isRSD() && ((RSD)sec).containsInfiniteElement()){
				 RSD tmp = (RSD)sec.clone();
				 tmp.replaceInfiniteElements();
				 delete.add(sec);
				 USEs.add(tmp);
				 foundInfinite = true;
			 }
			 else if(sec.isERSD() && ((ERSD)sec).get(0).containsInfiniteElement()){
				 RSD tmp = ((ERSD)sec).get(0).clone();
				 tmp.replaceInfiniteElements();
				 delete.add(sec);
				 SectionSet.ERSD ersd = ((ERSD)sec).clone();
				 ersd.remove(0);
				 ersd.add(0, tmp);
				 USEs.add(ersd);
				 foundInfinite = true;
			 }
		 }
		 if(foundInfinite){
			 for(SECTION sec:delete)
				 USEGlobal.get(s).remove(sec);
			 for(SECTION sec:USEs)
				 USEGlobal.get(s).add(sec);
		 }
	 } 
	 return USEGlobal;
 }
    
    private void printSECTIONsInProcedure(TranslationUnit tu, Procedure proc){
    	PCFGraph cfg = prog_record.get_PCFGraph(tu, proc);
    	//Map range_map = prog_record.get_range_map(tu, proc);
    	 TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
		 Iterator<DFANode> iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	    	 DFANode node = node_list.get(order);
	    	 if(isBarrierNode(node)){
	    		 AnnotationStatement ir = ((AnnotationStatement)node.getData(Arrays.asList("super-entry", "stmt")));
	    		 String type = (String) node.getData("type");
	    		 OmpdAnnotation barrier = ir.getAnnotation(OmpdAnnotation.class, "barrier");
	    		 int barrier_id = (Integer)barrier.get("barrier_id");
	    		 //if(ir.toString().contains("artificial"))
	    		//	 continue;
	    		 	 
	    		 SectionSet.MAP DEFlocal = (SectionSet.MAP)node.getData("must_def_in");
	    		 SectionSet.MAP KILL = (SectionSet.MAP)node.getData("KILL_in");
	    		 SectionSet.MAP USElocal = (SectionSet.MAP)node.getData("USElocal");
	    		 SectionSet.MAP USEGlobal = (SectionSet.MAP)node.getData("USEGlobal");
	    		 String info="barrier " + barrier_id + "\n";
	    		 if(DEFlocal!=null) info = info + "DEFlocal="+DEFlocal.toString();
	    		 if(KILL!=null) info = info + "\nKILL="+KILL.toString();
	    		 if(USElocal!=null) info = info + "\nUSElocal"+USElocal;
	    		 if(USEGlobal!=null) info = info + "\nUSEGlobal"+USEGlobal;
	    		 AnnotationStatement st1 = new AnnotationStatement(new CommentAnnotation(info));
	    		 IRTools.getAncestorOfType(ir, CompoundStatement.class).addStatementAfter(ir, st1);
	    	 }
	     }
    	
    }
    
    private void performCommunicationInProcedure(TranslationUnit tu, Procedure proc){
    	PCFGraph cfg = prog_record.get_PCFGraph(tu, proc);
    	 TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
		 Iterator<DFANode> iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	    	 DFANode node = node_list.get(order);
	    	 if(isBarrierNode(node)){
	    		 SectionSet.MAP DEFlocal = (SectionSet.MAP)node.getData("must_def_in");
	    		 SectionSet.MAP USEGlobal = (SectionSet.MAP)node.getData("USEGlobal");
	    		 if(DEFlocal==null || USEGlobal==null)
	    			 continue;
	    		 Set<Symbol> commonSymbols = new HashSet<Symbol>(); // common arrays exist in both: DEF and USE sets
	    		 for(Symbol s : DEFlocal.keySet())
	    			 if(USEGlobal.keySet().contains(s))
	    				 commonSymbols.add(s);
	    		 if(commonSymbols.isEmpty())
	    			 continue;
	    		 AnnotationStatement ir = ((AnnotationStatement)node.getData(Arrays.asList("super-entry", "stmt"))); //barrier statement
	    		 OmpdAnnotation barrier = ir.getAnnotation(OmpdAnnotation.class, "barrier");
	    		 int barrier_id = (Integer)barrier.get("barrier_id");
	    		 RangeDomain rd = (RangeDomain) node.getData("range_in");
	    		 
	    		 
	    		 //substitute Inifinite section in USEGlobal
	    		 SectionSet.MAP use_global;
	    		 if(Driver.getOptionValue("use-explicit-partitioning")!=null)
	    			 use_global = substituteInfiniteSections_xp(USEGlobal,commonSymbols,rd);
	    		 else
	    			 use_global = substituteInfiniteSections(USEGlobal,commonSymbols,rd);
	    		 if(use_global.hasChanged(USEGlobal, rd))
	    			 node.putData("USEGlobal", use_global); // in case infinite sections were present, then save the new substituted global use
	    		 
	    		 //library calls to pass DEF and USE sections for this barrier to the RUNTIME system
	    		 CompoundStatement cs;
	    		 if(Driver.getOptionValue("use-explicit-partitioning")!=null)
	    			  cs = optimized_passing_order_xp(DEFlocal,use_global,commonSymbols,rd,barrier_id);
	    		 else
	    			  cs = optimized_passing_order(DEFlocal,use_global,commonSymbols,rd,barrier_id);
	    		 
	    		 if(cs.countStatements()==0)
	    			 continue;
	    		 
	    		 for(Symbol s:commonSymbols){
	    			cs.addStatementBefore(IRTools.getFirstNonDeclarationStatement(cs), ompd_discard(barrier_id,s)); 
	    		 }
	    		 
	    		 
	    		 //find the accessed symbols in USE and DEF sections
	    		 Set<Symbol> accessedSymbols = new HashSet<Symbol>();
	    		 for(Symbol s: commonSymbols){
	    	    		for(SECTION def : DEFlocal.get(s)){
	    	    				accessedSymbols.addAll(getAccessedSymbols(def));
	    	    		}
	    	    		for(SECTION use : use_global.get(s)){
	    	    				accessedSymbols.addAll(getAccessedSymbols(use));
	    	    		}
	    	     }
	    		 
	    		//insert these library calls in the procedure as early as possible
	    		 insert_statements_AsEarlyAsPossible(cs,ir,accessedSymbols,proc);
	    		 
	    	    //library call to invoke communication at this barrier
	    		 Statement commStatement = ompd_barrier(barrier_id);
	    		 last_barrier_with_non_empty_comm = node;
	    		 //insert this library
	    		 ((CompoundStatement)IRTools.getAncestorOfType(ir, CompoundStatement.class)).addStatementAfter(ir, commStatement);
	    	 }
	     }
    }
    
    private Set<Symbol> getAccessedSymbols(SECTION sec){
    	if(sec.isRSD())
    		return getAccessedSymbols((RSD)sec);
    	else{
    		Set<Symbol> tmp=new HashSet<Symbol>();
        	for(RSD e: (ERSD) sec)
        		tmp.addAll(getAccessedSymbols(e));
        	return tmp;
    	}
    }
    private Set<Symbol> getAccessedSymbols(RSD rsd){
    	Set<Symbol> tmp=new HashSet<Symbol>();   	
    	for(int i=0; i<rsd.size();i++){
    		ELEMENT e=rsd.get(i);
    		tmp.addAll(DataFlowTools.getUseSymbol(e.getLB()));
    		tmp.addAll(DataFlowTools.getUseSymbol(e.getUB()));
    		tmp.addAll(DataFlowTools.getUseSymbol(e.getSTRIDE()));
    	}
    	return tmp;
    }
    
    /* insert the statements "cs" as early as possible in the procedure body "proc". 
     * "useSymbols" is the set of accessed symbols in the original statement "orig"
     * */
    private void insert_statements_AsEarlyAsPossible(CompoundStatement cs, Statement orig, Set<Symbol> accessedSymbols, Procedure proc){
    	//find the earliest position of where to insert "cs" 
    	Statement position=null;
        CompoundStatement position_scope=null;
    	boolean DefinedInLoopStatementParameters=false;

        if(accessedSymbols.isEmpty()) {
        	position = IRTools.getLastDeclarationStatement(proc.getBody());
        	position_scope = proc.getBody();
        	DefinedInLoopStatementParameters = false;
        }
        else{
        	Statement last=null;
            Statement prev_scope= orig;
            Statement scope = IRTools.getAncestorOfType(prev_scope, CompoundStatement.class);
            while(true){
                last = getLastDefBeforeStatement((CompoundStatement)scope, prev_scope, accessedSymbols);
                if(last != null){
                	position = last;
                	DefinedInLoopStatementParameters = false;
                	position_scope = (CompoundStatement) scope;
                	break;
                }
                if(scope.equals(proc.getBody())) break;
                if(scope.getParent() instanceof Loop){
                	prev_scope = (Statement) scope.getParent();
                	if(isDefinedInLoopStatementParameters((ForLoop) scope.getParent() ,accessedSymbols)){
                		position = prev_scope;
                		DefinedInLoopStatementParameters = true;
                		position_scope = (CompoundStatement) scope;
                		break;
                	}
                }
                else 
                	prev_scope = scope;
                
                scope = IRTools.getAncestorOfType(prev_scope, CompoundStatement.class);
            }
        	
            if(position==null){
            	// if bounds never initialized within proc, then compiler assumes it is preknown
                position = IRTools.getLastDeclarationStatement(proc.getBody());
                DefinedInLoopStatementParameters = false;
                position_scope = proc.getBody();   	
            }  	
        }
        
        if(DefinedInLoopStatementParameters)
        	position_scope.addStatementBefore(IRTools.getFirstNonDeclarationStatement(position_scope), cs);
        else 
        	position_scope.addStatementAfter(position, cs);
    }
    
    
    /**
     * Returns the last statement that defines any of the symbols in wanted before the
     * occurrence of Statement e within the block t. returns null if such a statement does not exist
     */
    private Statement getLastDefBeforeStatement(CompoundStatement t, Statement e, Set<Symbol> wanted) {
        Statement last=null;
        FlatIterator iter = new FlatIterator(t);
        while (iter.hasNext()) {
            Statement o = (Statement)iter.next();
            if(o.equals(e)) break;
            Set<Symbol> smbls = DataFlowTools.getDefSymbol(o);
            for(Symbol s: smbls){
            	for(Symbol ss : wanted)
            		if(s.equals(ss)) {last=o; break;}
            }
        }
        return last;
    } 
    
    private boolean isDefinedInLoopStatementParameters(Loop loop, Set<Symbol> wanted){
    	Symbol index=LoopTools.getLoopIndexSymbol(loop);
    	for(Symbol ss : wanted)
    		if(ss.equals(index)) return true;
    	return false;
    }
    
    private CompoundStatement optimized_passing_order(SectionSet.MAP DEFlocal, SectionSet.MAP USEGlobal, Set<Symbol> commonSymbols, RangeDomain rd, int barrier_id){
    	CompoundStatement cs = new CompoundStatement();
    	
    	 for(Symbol s: commonSymbols){  // start with normal def sections
    		 
    		 Map<SECTION,SectionSet> comm = new HashMap<SECTION,SectionSet>(); // maps def to their relevent use that participate in communicaion
    		
    		 for(SECTION def : DEFlocal.get(s)){
    			 
    			 SectionSet USEs = new SectionSet(); /// relevant use set to this def

    			 if(USEGlobal.keySet().contains(s)){
    				 for(SECTION use : USEGlobal.get(s)){
        				 if(def.isIndependent(use, rd))
    						 continue; // disjoint -- no communication
        				 if(use.isParallel()){
    						//detect self communication
        					if(OMPDTools.do_both_have_same_partitioned_dimension(def,use,rd))
        						continue;
        					else
        						 USEs.add(use);
    					}
    					else { // use is serial
    							 USEs.add(use);
    					} 
        			 }
    			 }
    			 
    			 
    			 for(SECTION use: USEs.clone()){
					 if(use.isERSD()){ // for ERSD expression, remove right terms that are disjoint from def because they do not affect communication 
						 SectionSet right_terms_to_be_kept = new SectionSet();
						 boolean at_least_one_tern_was_removed = false;
						 for(int i=1; i<((SectionSet.ERSD)use).size();i++)
							 if(((SectionSet.ERSD)use).get(i).isIndependent(def, rd)==false)
								 right_terms_to_be_kept.add(((SectionSet.ERSD)use).get(i));
							 else
								 at_least_one_tern_was_removed = true;
							 
						 if(at_least_one_tern_was_removed){
							 SectionSet.ERSD e = new SectionSet.ERSD();
							 e.add(0,((SectionSet.ERSD)use).get(0));
							 for(SECTION sec: right_terms_to_be_kept)
								 e.add((RSD)sec);
							 USEs.remove(use);
							 if(e.size()>1)
								USEs.add(e);
							 else
								 USEs.add(e.get(0));
						 }
					 }
				 }
    			 if(USEs.isEmpty())
					 continue;
				 if(!InitializedSymbols.contains(s))
					 InitializedSymbols.add(s);
    			 comm.put(def, USEs); // establish a communication between def and uses in USEs set.
    		 }
    		 
    		 //now: comm structure should be ready
    		 if(comm.isEmpty())
    			 continue;
    		
    		 for(SECTION def: comm.keySet()){
    			 if(comm.get(def).isEmpty())
    				 continue;
    			 add_def_statement_to_cs(cs,s,barrier_id,def,rd);
    			 for(SECTION use: comm.get(def))
    				 add_use_statement_to_cs(cs,s,barrier_id,use,rd);
    			 cs.addStatement(ompd_messages(barrier_id));
				 cs.addStatement(ompd_purge_sections(barrier_id,"DEFlocal"));
				 cs.addStatement(ompd_purge_sections(barrier_id,"USEglobal"));
    		 }
    		 
    	 } 
    	 
    	 
    	 
		 return cs;
    }
    
    private void add_def_statement_to_cs(CompoundStatement cs, Symbol s, int barrier_id, SECTION def, RangeDomain rd){
		 if(def.isRSD())
			 cs.addStatement(ompd_pass_parallel_section_reuse_pi(barrier_id, s, "DEFlocal", (RSD)def));
		 else
			 cs.addStatement(ompd_pass_parallel_ersd_reuse_pi(barrier_id, s, "DEFlocal", (ERSD)def));
    }
    private void add_use_statement_to_cs(CompoundStatement cs, Symbol s, int barrier_id, SECTION use, RangeDomain rd){
    	if(use.isParallel()){
    		if(use.isRSD())
				 cs.addStatement(ompd_pass_parallel_section_reuse_pi(barrier_id, s, "USEglobal", (RSD)use));
			 else
				 cs.addStatement(ompd_pass_parallel_ersd_reuse_pi(barrier_id, s, "USEglobal", (ERSD)use));
		 }
		 else { // use is serial
			 if(use.isRSD())
				 cs.addStatement(ompd_pass_serial_section(barrier_id, s, "USEglobal", (RSD)use));
			 else // needed in the case inifnite ersd sections 
				 cs.addStatement(ompd_pass_serial_ersd(barrier_id, s, "USEglobal", (ERSD)use));
		 }
    }  
    
    private CompoundStatement optimized_passing_order_xp(SectionSet.MAP DEFlocal, SectionSet.MAP USEGlobal, Set<Symbol> commonSymbols, RangeDomain rd, int barrier_id){
    	CompoundStatement cs = new CompoundStatement();
		 for(Symbol s: commonSymbols){
			 for(SECTION def : DEFlocal.get(s)){
				 if(def.isSerial())
					 continue; // no communication for a redundant def
				 SectionSet USEs = new SectionSet(); /// relevant use set to this def
				 for(SECTION use : USEGlobal.get(s)){
					 if(def.isRSD() && use.isRSD()){
						 if(def.isIndependent(use, rd))
							 continue; // disjoint -- no communication
					 }
					 else if(def.isRSD() && use.isERSD()){
						 if(def.isIndependent(((SectionSet.ERSD)use).get(0), rd))
							 continue;
						 /*for(int i=1; i<((SectionSet.ERSD)use).size();i++)
							 if(def.get_parallel_dim()==((SectionSet.ERSD)use).get(i).get_parallel_dim() && OMPDParallelForLoop.IsSimilar(def.get_pfor(), ((SectionSet.ERSD)use).get(i).get_pfor(), rd) )
								 if(def.isSubsetOf(((SectionSet.ERSD)use).get(i), rd))
									 continue;*/
					 }
					 else if(def.isERSD() && use.isRSD()){
						 if(use.isIndependent(((SectionSet.ERSD)def).get(0), rd))
							 continue;
					 }
					 else if(def.isERSD() && use.isERSD()){
						 if(((SectionSet.ERSD)def).get(0).isIndependent(((SectionSet.ERSD)use).get(0), rd))
							 continue;
					 }
					 

					 if(use.isParallel()){
						 if( def.get_parallel_dim()==use.get_parallel_dim() && 
								 (
								    (def.isRSD() && use.isRSD() && ELEMENT.isEqual(((RSD)def).get(def.get_parallel_dim()), ((RSD)use).get(use.get_parallel_dim()), rd)) ||
								    (def.isRSD() && use.isERSD() && ELEMENT.isEqual(((RSD)def).get(def.get_parallel_dim()), ((ERSD)use).get(0).get(use.get_parallel_dim()), rd)) ||
								    (def.isERSD() && use.isRSD() && ELEMENT.isEqual(((ERSD)def).get(0).get(def.get_parallel_dim()), ((RSD)use).get(use.get_parallel_dim()), rd)) ||
								    (def.isERSD() && use.isERSD() && ELEMENT.isEqual(((ERSD)def).get(0).get(def.get_parallel_dim()), ((ERSD)use).get(0).get(use.get_parallel_dim()), rd))
								 )
							)
								 continue; // self communication -- save it
						 else{
							 USEs.add(use);
						 }
					 }
					 else { // use is serial
						 USEs.add(use);
					 }
				 }
				 if(USEs.isEmpty())
					 continue;
				 if(!InitializedSymbols.contains(s))
					 InitializedSymbols.add(s);
				 
				 if(def.isRSD())
					 cs.addStatement(ompd_pass_parallel_section_reuse_pi(barrier_id, s, "DEFlocal", (RSD)def));
				 else
					 cs.addStatement(ompd_pass_parallel_ersd_reuse_pi(barrier_id, s, "DEFlocal", (ERSD)def));
				 for(SECTION use : USEs){
					 if(use.isParallel()){
						 if(use.isRSD())
							 cs.addStatement(ompd_pass_parallel_section_reuse_pi(barrier_id, s, "USEglobal", (RSD)use));
						 else
							 cs.addStatement(ompd_pass_parallel_ersd_reuse_pi(barrier_id, s, "USEglobal", (ERSD)use));
					 }
					 else { // use is serial
						 if(use.isRSD())
							 cs.addStatement(ompd_pass_serial_section(barrier_id, s, "USEglobal", (RSD)use));
						 else // needed in the case inifnite ersd sections 
							 cs.addStatement(ompd_pass_serial_ersd(barrier_id, s, "USEglobal", (ERSD)use));
					 }
					 
				 }
				 cs.addStatement(ompd_messages(barrier_id));
				 cs.addStatement(ompd_purge_sections(barrier_id,"DEFlocal"));
				 cs.addStatement(ompd_purge_sections(barrier_id,"USEglobal"));
			 }
			 //cs.addStatement(ompd_messages(barrier_id));
			 //cs.addStatement(ompd_purge_sections(barrier_id,"DEFlocal"));
			 //cs.addStatement(ompd_purge_sections(barrier_id,"USEglobal"));
		 }
		 /*if(cs.countStatements()!=0){
			 cs.addStatement(ompd_messages(barrier_id));
			 cs.addStatement(ompd_purge_sections(barrier_id,"DEFlocal"));
			 cs.addStatement(ompd_purge_sections(barrier_id,"USEglobal"));
		 }*/
		 return cs;
    }
    
    private Statement ompd_partition(Expression orig_lb, Expression orig_ub, Expression orig_step, Identifier pi){
    	NameID fcname = new NameID("ompd_partition");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(orig_lb); arg_list.add(orig_ub); arg_list.add(orig_step);
        fc.setArguments(arg_list);
        AssignmentExpression func_call = new AssignmentExpression(pi,AssignmentOperator.NORMAL,fc);
        ExpressionStatement func_call_stmt = new ExpressionStatement(func_call);
        return new AnnotationStatement(new CodeAnnotation(func_call_stmt.toString()));
    }
    private Expression ompd_partition(Expression orig_lb, Expression orig_ub, Expression orig_step){
    	NameID fcname = new NameID("ompd_partition");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(orig_lb.clone()); arg_list.add(orig_ub.clone()); arg_list.add(orig_step.clone());
        fc.setArguments(arg_list);
        return fc;
    }
    private Statement ompd_print_bounds(int ID, Identifier pi) {
    	NameID fcname2 = new NameID ("ompd_print_bounds");
        FunctionCall fc2 = new FunctionCall(fcname2);
        LinkedList<Expression> arg_list2 = new LinkedList<Expression>();
        arg_list2.add(new IntegerLiteral(ID)); arg_list2.add(pi);
        fc2.setArguments(arg_list2);
        ExpressionStatement func_call_stmt2 = new ExpressionStatement(fc2);
        IfStatement ifStatement = new IfStatement(new Identifier(new VariableDeclarator(new NameID("OMPD_PRINT_BOUNDS"))), func_call_stmt2 ); 
        return ifStatement;
    }
    private Statement ompd_pass_parallel_section(int barrier_id, Symbol s, String type, RSD rsd){
    	NameID fcname = new NameID("ompd_pass_parallel_section");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        arg_list.add(new IntegerLiteral(rsd.get_parallel_dim()));
        arg_list.add(ompd_partition(rsd.get(rsd.get_parallel_dim()).getLB().clone(), rsd.get(rsd.get_parallel_dim()).getUB().clone(), rsd.get(rsd.get_parallel_dim()).getSTRIDE() ));
        
        for(int i=0; i<rsd.get_dim_size();i++){
        	if(i!=rsd.get_parallel_dim()){
        		arg_list.add(rsd.get(i).getLB().clone());
        		arg_list.add(rsd.get(i).getUB().clone());
        		arg_list.add(rsd.get(i).getSTRIDE().clone());
        	}
        }
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }  
    private Statement ompd_pass_parallel_section_reuse_pi(int barrier_id, Symbol s, String type, RSD rsd){
    	NameID fcname = new NameID("ompd_pass_parallel_section");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        arg_list.add(new IntegerLiteral(rsd.get_parallel_dim()));
        if(rsd.get_pfor().IsRepetitive()){
        	Expression offset = Symbolic.subtract(rsd.get(rsd.get_parallel_dim()).getLB(),rsd.get_pfor().get_orig_lb());
            Expression coeff = rsd.get_parallel_coeff().clone();
            arg_list.add(pi_of(offset,coeff,new NameID("ompd_pi"+rsd.get_pfor().get_loopId())));
        }
        else{
        	Expression lb_offset = Symbolic.subtract(rsd.get(rsd.get_parallel_dim()).getLB(),rsd.get_pfor().get_orig_lb());
        	Expression ub_offset = Symbolic.subtract(rsd.get(rsd.get_parallel_dim()).getUB(),rsd.get_pfor().get_orig_ub());
        	if((new RangeDomain()).isEQ(lb_offset, ub_offset) && (new RangeDomain()).isEQ(rsd.get(rsd.get_parallel_dim()).getSTRIDE() , rsd.get_pfor().get_step()) ){
        		Expression coeff = rsd.get_parallel_coeff().clone();
                arg_list.add(pi_of(lb_offset,coeff,new NameID("ompd_pi"+rsd.get_pfor().get_loopId())));
        	}
        	else{ 
        		arg_list.add(ompd_partition(rsd.get(rsd.get_parallel_dim()).getLB().clone(), rsd.get(rsd.get_parallel_dim()).getUB().clone(), rsd.get(rsd.get_parallel_dim()).getSTRIDE() ));
        	}
        }
        
        for(int i=0; i<rsd.get_dim_size();i++){
        	if(i!=rsd.get_parallel_dim()){
        		arg_list.add(rsd.get(i).getLB().clone());
        		arg_list.add(rsd.get(i).getUB().clone());
        		arg_list.add(rsd.get(i).getSTRIDE().clone());
        	}
        }
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }   
    private Statement ompd_pass_serial_section(int barrier_id, Symbol s, String type, RSD rsd){
    	NameID fcname = new NameID("ompd_pass_serial_section");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        for(int i=0; i<rsd.get_dim_size();i++){
        	arg_list.add(rsd.get(i).getLB().clone());
    		arg_list.add(rsd.get(i).getUB().clone());
    		arg_list.add(rsd.get(i).getSTRIDE().clone());
        }
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_pass_parallel_ersd(int barrier_id, Symbol s, String type, ERSD ersd){
    	NameID fcname = new NameID("ompd_pass_parallel_ersd");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        arg_list.add(new IntegerLiteral(ersd.get_parallel_dim()));
        arg_list.add(ompd_partition(ersd.get(0).get(ersd.get_parallel_dim()).getLB().clone(), ersd.get(0).get(ersd.get_parallel_dim()).getUB().clone(), ersd.get(0).get(ersd.get(0).get_parallel_dim()).getSTRIDE().clone() ));
        
        arg_list.add(new IntegerLiteral(ersd.size()));
        for(int j=0;j<ersd.size();j++){
        	RSD rsd = ersd.get(j);
        	for(int i=0; i<rsd.get_dim_size();i++){
            	if(!(j==0 && i==rsd.get_parallel_dim())){
            		arg_list.add(rsd.get(i).getLB().clone());
            		arg_list.add(rsd.get(i).getUB().clone());
            		arg_list.add(rsd.get(i).getSTRIDE().clone());
            	}
            }
        }
        
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_pass_parallel_ersd_reuse_pi(int barrier_id, Symbol s, String type, ERSD ersd){
    	NameID fcname = new NameID("ompd_pass_parallel_ersd");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        arg_list.add(new IntegerLiteral(ersd.get_parallel_dim()));
        if(ersd.get_pfor().IsRepetitive()){
        	Expression offset = Symbolic.subtract(ersd.get(0).get(ersd.get_parallel_dim()).getLB(),ersd.get_pfor().get_orig_lb());
            Expression coeff = ersd.get_parallel_coeff().clone();
            arg_list.add(pi_of(offset,coeff,new NameID("ompd_pi"+ersd.get_pfor().get_loopId())));
        }
        else{
        	Expression lb_offset = Symbolic.subtract(ersd.get(0).get(ersd.get_parallel_dim()).getLB(),ersd.get_pfor().get_orig_lb());
        	Expression ub_offset = Symbolic.subtract(ersd.get(0).get(ersd.get_parallel_dim()).getUB(),ersd.get_pfor().get_orig_ub());
        	if((new RangeDomain()).isEQ(lb_offset, ub_offset) && (new RangeDomain()).isEQ(ersd.get(0).get(ersd.get_parallel_dim()).getSTRIDE() , ersd.get_pfor().get_step())){
        		Expression coeff = ersd.get_parallel_coeff().clone();
                arg_list.add(pi_of(lb_offset,coeff,new NameID("ompd_pi"+ersd.get_pfor().get_loopId())));
        	}
        	else{ 
        		arg_list.add(ompd_partition(ersd.get(0).get(ersd.get_parallel_dim()).getLB().clone(), ersd.get(0).get(ersd.get_parallel_dim()).getUB().clone(), ersd.get(0).get(ersd.get(0).get_parallel_dim()).getSTRIDE().clone() ));
        	}
        }
        
        arg_list.add(new IntegerLiteral(ersd.size()));
        for(int j=0;j<ersd.size();j++){
        	RSD rsd = ersd.get(j);
        	for(int i=0; i<rsd.get_dim_size();i++){
            	if(!(j==0 && i==rsd.get_parallel_dim())){
            		arg_list.add(rsd.get(i).getLB().clone());
            		arg_list.add(rsd.get(i).getUB().clone());
            		arg_list.add(rsd.get(i).getSTRIDE().clone());
            	}
            }
        }
        
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    
    private Statement ompd_pass_serial_ersd(int barrier_id, Symbol s, String type, ERSD ersd){
    	NameID fcname = new NameID("ompd_pass_serial_ersd");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(new NameID(type));
        arg_list.add(new IntegerLiteral(ersd.size()));
        for(int j=0;j<ersd.size();j++){
        	RSD rsd = ersd.get(j);
        	for(int i=0; i<rsd.get_dim_size();i++){
        		arg_list.add(rsd.get(i).getLB().clone());
        		arg_list.add(rsd.get(i).getUB().clone());
        		arg_list.add(rsd.get(i).getSTRIDE().clone());
            }
        }
        
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    
    private FunctionCall pi_of(Expression offset, Expression coeff, Expression pi){
    	NameID fcname = new NameID("pi_of");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(offset); arg_list.add(coeff); arg_list.add(pi);
        fc.setArguments(arg_list);
        return fc;
    }    
    private Statement ompd_messages(int barrier_id){
    	NameID fcname = new NameID("ompd_messages");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_barrier(int barrier_id){
    	NameID fcname = new NameID("ompd_barrier");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id));
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_purge_sections(int barrier_id, String type){
    	NameID fcname = new NameID("ompd_purge_sections");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id)); arg_list.add(new NameID(type));
        fc.setArguments(arg_list);  
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_discard(int barrier_id, Symbol s){
    	NameID fcname = new NameID("ompd_discard");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new IntegerLiteral(barrier_id)); arg_list.add(new NameID(s.getSymbolName()));
        fc.setArguments(arg_list); 
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_discard_partition(NameID pi_id){
    	NameID fcname = new NameID("ompd_discard_partition");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(pi_id);
        fc.setArguments(arg_list); 
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    private Statement ompd_init_symbol(Symbol s){
    	NameID fcname = new NameID("ompd_init_symbol");
        FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        arg_list.add(new NameID(s.getSymbolName()));
        arg_list.add(getMPIType(s));
        ArraySpecifier specifier = (ArraySpecifier)s.getArraySpecifiers().get(0);
        arg_list.add(new IntegerLiteral(specifier.getNumDimensions()));
        for(int i=0; i<specifier.getNumDimensions();i++)
        	arg_list.add(specifier.getDimension(i).clone());
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
    	return func_call_stmt;
    }
    
    private void Initialize_Symbols(CompoundStatement procbody){
    	List<DeclarationStatement> set= IRTools.getStatementsOfType(procbody, DeclarationStatement.class);
    	for(Symbol s:InitializedSymbols){
    		boolean found=false;
    		for(DeclarationStatement decl: set){
    			if(decl.getDeclaration().equals(s.getDeclaration())){
    				CompoundStatement parent=IRTools.getAncestorOfType(s.getDeclaration().getParent(), CompoundStatement.class);
    				parent.addStatementBefore(IRTools.getFirstNonDeclarationStatement(parent), ompd_init_symbol(s));
    				found=true;
    				break;
    			}
    		}
    		if(found==false)
    			procbody.addStatementAfter(IRTools.getLastDeclarationStatement(procbody), ompd_init_symbol(s));
    	}
    }
    
    private void finialize(){
    	substituteOMPcalls();
   	 	insertHeader(); 
   	 	insertOMPDStartup();
   	 	insertOMPDExit(); 
   	 	this.program.addTranslationUnit(globals); // ompd_globals.h
    }
    
 
    private void substituteOMPcalls(){
    	 for (TranslationUnit tu : prog_record.get_TUs()) {
	            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
	            	FlatIterator iter = new FlatIterator(proc.getBody());
	                while (iter.hasNext()) {
	                    Statement o = (Statement)iter.next();
	                    List<FunctionCall> ac_lst = IRTools.getExpressionsOfType(o, FunctionCall.class);
	                    if(!ac_lst.isEmpty())
	                    	for(FunctionCall call: ac_lst)
	                    		if(call.toString().startsWith("omp_get")){
	                    			if(call.toString().startsWith("omp_get_thread_num"))
	                    				IRTools.replaceAll(o, call, new Identifier(prog_record.get_procid()));
	                    			else if(call.toString().startsWith("omp_get_num_threads"))
	                    				IRTools.replaceAll(o, call, new Identifier(prog_record.get_nprocs()));
	                    			else if(call.toString().startsWith("omp_get_max_threads"))
	                    				IRTools.replaceAll(o, call, new Identifier(prog_record.get_nprocs()));
	                    			else if(call.toString().startsWith("omp_get_wtime"))
	                    				IRTools.replaceAll(o, call, new FunctionCall(new NameID("MPI_Wtime")));
	                    		}
	                }
	            }
	        }
    }

    private void insertHeader() {
        String header_code = "#include \"ompd_interface.h\"";
        CodeAnnotation code_annot = new CodeAnnotation(header_code);
        AnnotationDeclaration anote = new AnnotationDeclaration(code_annot);
        globals.addDeclarationFirst(anote);
        
        String v = "int _var_;";
        CodeAnnotation code_annot2 = new CodeAnnotation(v);
        AnnotationDeclaration anote2 = new AnnotationDeclaration(code_annot2);
        globals.addDeclaration(anote2);
        
        String globals_header = "#include \"ompd_globals.h\"";
        CodeAnnotation globals_annot = new CodeAnnotation(globals_header);
        AnnotationDeclaration globals_anote = new AnnotationDeclaration(globals_annot);
        
        for (TranslationUnit tu : prog_record.get_TUs()) {
        	tu.addDeclarationFirst(globals_anote);
        	//tu.addDeclarationFirst(anote);
        }
    }
    
    private void insertOMPDStartup(){
    	int i;
    	NameID fcname = new NameID("ompd_startup");
    	FunctionCall fc = new FunctionCall(fcname);
        LinkedList<Expression> arg_list = new LinkedList<Expression>();
        List<VariableDeclaration> main_args = mainProc.getParameters();
        for(VariableDeclaration dec: main_args){
        	for(i=0;i<dec.getNumDeclarators();i++){
        		arg_list.add(new UnaryExpression ( UnaryOperator.ADDRESS_OF,new Identifier ((VariableDeclarator) dec.getDeclarator(i))) );
        	}
        }
       // arg_list.add(new UnaryExpression (UnaryOperator.ADDRESS_OF, new Identifier (nprocs_symbol) ) ); 
       // arg_list.add(new UnaryExpression (UnaryOperator.ADDRESS_OF, new Identifier (procid_symbol) ) );
        NameID comm_id = new NameID("MPI_COMM_WORLD");
        VariableDeclarator comm_declarator = new VariableDeclarator(comm_id);
        arg_list.add(new Identifier (comm_declarator));
        fc.setArguments(arg_list);
        ExpressionStatement func_call_stmt = new ExpressionStatement(fc);
        mainProc.getBody().addStatementBefore(IRTools.getFirstNonDeclarationStatement(mainProc.getBody()), func_call_stmt );
    }
  
  //This function is copied from CommAnalysis.java
    private void insertOMPDExit() {
        /*
          ** Two cases:
          ** 1) Before every exit() call.
          ** 2) Before every return call in the main() function.
          */
        // TO-DO: CASE 1

        //////////////////////////////////////////////////////////////////////
        // CASE 2
        //////////////////////////////////////////////////////////////////////

        // CASE 2.1
        // Insert before every return statement

        if (mainProc == null) return;

        BreadthFirstIterator bfs_iter = new BreadthFirstIterator(mainProc);
        bfs_iter.pruneOn(ReturnStatement.class);

        // TODO: use code annotation.
        String func_str = "ompd_exit(0);";
        CodeAnnotation ca = new CodeAnnotation(func_str);
        AnnotationStatement as = new AnnotationStatement(ca);
        
        //String func_str2 = "ompd_statistics();";
        //CodeAnnotation ca2 = new CodeAnnotation(func_str2);
        //AnnotationStatement as2 = new AnnotationStatement(ca2);

        for (; ;) {
            ReturnStatement stmt = null;
            try {
                stmt = (ReturnStatement) bfs_iter.next(ReturnStatement.class);
                CompoundStatement parent = (CompoundStatement) stmt.getParent();
                parent.addStatementBefore(stmt, as);
                //parent.addStatementBefore(as, as2);
            } catch (NoSuchElementException e) {
                break;
            }
        }

        // CASE 2.2
        // If the final statement is not return, insert ompd_exit(1)
        // after the final statement.

        // Find the last statement
        CompoundStatement funcBody = mainProc.getBody();
        Traversable t = null;
        List<Traversable> children = funcBody.getChildren();

        if (children.isEmpty())
            Tools.exit("ERROR, main must have at least two statements: ompd_startup(), ompd_init_loop_bounds()");

        t = children.get(children.size() - 1);

        if (t == null) {
            funcBody.addStatementAfter((Statement) t, as);
            //funcBody.addStatementAfter((Statement) as2, as);
        }
        else {
            println("The last stmt = " + t.getClass().toString(), 2);
            if (t.getClass() == ReturnStatement.class) {

            }
            else {
            	funcBody.addStatementAfter((Statement) t, as);
                //funcBody.addStatementAfter((Statement) as2, as);
            }
        }
    }
    
    private boolean isBarrierNode(DFANode node) {
        String tag = (String) node.getData("tag");
        if (tag != null && tag.equals("barrier")) {
            return true;
        }
        return false;
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
   
}
