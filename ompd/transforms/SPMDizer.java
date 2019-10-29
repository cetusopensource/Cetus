package ompd.transforms;  


import java.util.*;

import ompd.analysis.PCFGraph;
import ompd.hir.OMPDParallelForLoop;
import ompd.hir.OMPDTools;
import ompd.hir.OmpdAnnotation;
import cetus.analysis.DFAGraph;
import cetus.analysis.DFANode;
import cetus.analysis.LoopTools;
import cetus.analysis.RangeAnalysis;
import cetus.exec.Driver;
import cetus.hir.*;
import cetus.analysis.RangeDomain;

public class SPMDizer {
	
    private int barrier_id;
    private int num_barriers;
    private ProgramRecord prog_record;
    private boolean foundNonRepetitiveLoop;
	
	public SPMDizer(ProgramRecord rcd) {
		prog_record = rcd;
		foundNonRepetitiveLoop = false;
    }
	
	public void start() {
		barrier_id = 0;
		num_barriers=0;
		for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
                parallelizeLoopsInProcedure(tu,proc);
                DetermineOuterSerialLoops(tu,proc);
                InsertArtificialBarriers(tu,proc);
                createPCFG(tu,proc);
                tagBarrierIDsInProcedure(tu,proc);
                if(!prog_record.IsRepetitiveProgram())
                	DetermineRepetitiveLoops(tu,proc);
                countSharedArrayAcesses(tu,proc);
            }
        }
		PrintTools.println("Total number of static barriers is " + num_barriers, 0);
		if(Driver.getOptionValue("non-repetitive")==null) // detect repetitivness only if user allowed the compiler
			 if(!foundNonRepetitiveLoop)
				 prog_record.MakeRepetitiveProgram();
    }
	
	private boolean Testifeligible(ForLoop loop){
		 if (!LoopTools.isCanonical(loop)) return false;
		 //ToDo: check if all array accesses have independent dimensions' subscripts   
		 return true;
	}
	
	private void parallelizeLoopsInProcedure(TranslationUnit tu, Procedure proc){
		
		List<OmpdAnnotation> annotationList = IRTools.collectPragmas(proc, OmpdAnnotation.class, "for");
		for (OmpdAnnotation annotation : annotationList) {
            ForLoop loop = (ForLoop) annotation.getAnnotatable();
            if(Testifeligible(loop)){
            	OMPDParallelForLoop pfor = new OMPDParallelForLoop(loop);
            	/*RangeDomain rng = (RangeDomain) prog_record.get_range_map(tu, proc).get((Statement)loop);
            	Statement position = pfor.find_position_of_partitioning_code(proc,rng );*/
            	if(prog_record.IsRepetitiveProgram())
            		pfor.MakeRepetitive(); 
            	prog_record.add_loop_to_proc_in_tu(tu, proc, annotation, pfor);           	           	
            }
            else{
            	//loop is serialized
            	loop.removeAnnotations(OmpdAnnotation.class);
            	//the compiler keeps the barrier after the loop that is forced to be serial 
            }
		}
		 PrintTools.println("Parallel Loops are parallelized using Pi-Operators ", 0);
	}
	
	private void DetermineOuterSerialLoops(TranslationUnit tu, Procedure proc) {
		DepthFirstIterator iter = new DepthFirstIterator(proc.getBody());
		ArrayList<Loop> OuterSerialLoops = new ArrayList<Loop>();
		int i;
		 while (iter.hasNext()) {
			    Object o = iter.next();
	            if (o instanceof Loop){
	            	Statement st = ((Loop)o).getBody();
	            	List<OmpdAnnotation> annotationList = IRTools.collectPragmas(st, OmpdAnnotation.class, "for");
	            	if(!annotationList.isEmpty()){
	            		OuterSerialLoops.add((Loop)o);
	            		if(!prog_record.IsRepetitiveProgram()){ 
	            			for(OmpdAnnotation annot: annotationList){
	            				prog_record.get_loop_record(tu, proc, annot).set_outer_serial_loop((Loop)o);
	            				//boolean isRepetitive = test_if_repetitive((Loop)o, annot, prog_record.get_loop_record(tu, proc, annot));
	            	    	}
	            		}
	            	} 
	            	/*else {
	            		List<OmpdAnnotation> annotationList1 = IRTools.collectPragmas(st, OmpdAnnotation.class, "parallel");
	            		if(!annotationList1.isEmpty())
	            			OuterSerialLoops.add((Loop)o);
	            	}*/
	            }
		 }
		 
		 //prog_record.set_OuterSerialLoopsSet(tu, proc, OuterSerialLoops);
		 
		 for(i=0;i<OuterSerialLoops.size();i++){
			//Add a barrier after the exit of the serial loop 
			OmpdAnnotation ompdAnnotation = new OmpdAnnotation();
     	    ompdAnnotation.put("barrier", "serial_loop_after");
     	    ompdAnnotation.put("source", OuterSerialLoops.get(i));
     	    CompoundStatement parent = IRTools.getAncestorOfType((Statement)OuterSerialLoops.get(i), CompoundStatement.class);
     	    parent.addStatementAfter((Statement)OuterSerialLoops.get(i), new AnnotationStatement(ompdAnnotation));
     	    
     	    //Add an artificial barrier before the entry of the serial loop
     	   OmpdAnnotation bfr = new OmpdAnnotation();
     	   bfr.put("barrier", "serial_loop_before");
   	       bfr.put("source", OuterSerialLoops.get(i));
   	       parent.addStatementBefore((Statement)OuterSerialLoops.get(i), new AnnotationStatement(bfr));
     	    
     	    //Add artificial barriers at the beginning and the end of the serial loop
     	    OmpdAnnotation up = new OmpdAnnotation();
     	    up.put("barrier", "serial_loop_up");
     	    up.put("source", OuterSerialLoops.get(i));
     	    OmpdAnnotation down = new OmpdAnnotation();
     	    down.put("barrier", "serial_loop_down");
     	    down.put("source", OuterSerialLoops.get(i));
     	    ((CompoundStatement)OuterSerialLoops.get(i).getBody()).addStatementBefore(IRTools.getFirstNonDeclarationStatement(OuterSerialLoops.get(i).getBody()), new AnnotationStatement(up));
     	    ((CompoundStatement)OuterSerialLoops.get(i).getBody()).addStatement(new AnnotationStatement(down));
		 }
		 
		 PrintTools.println("Number of Outerserial Loops is " + OuterSerialLoops.size(), 0);
		
	}
	
	private void InsertArtificialBarriers(TranslationUnit tu, Procedure proc) {
		DepthFirstIterator iter = new DepthFirstIterator(proc.getBody());
		ArrayList<CompoundStatement> eligible = new ArrayList<CompoundStatement>();
		 while (iter.hasNext()) {
			    Object o = iter.next();
			    if(o instanceof IfStatement){
			    	Statement if_ = ((IfStatement)o).getThenStatement();
			    	Statement else_ = ((IfStatement)o).getElseStatement();
			    	
			    	List<OmpdAnnotation> if_annotationList = IRTools.collectPragmas(if_, OmpdAnnotation.class, "for");
			    	if(!if_annotationList.isEmpty())
			    		eligible.add((CompoundStatement)if_);
			    	if(else_!=null){
			    		List<OmpdAnnotation> else_annotationList = IRTools.collectPragmas(else_, OmpdAnnotation.class, "for");
				    	if(!else_annotationList.isEmpty())
				    		eligible.add((CompoundStatement)else_);
			    	}
			    }
		 }
		 
		 for(int i=0;i<eligible.size();i++){
			 OmpdAnnotation at = new OmpdAnnotation();
	     	 at.put("barrier", "artificial");
	     	eligible.get(i).addStatementBefore(IRTools.getFirstNonDeclarationStatement(eligible.get(i)), new AnnotationStatement(at));
		 }
	}
	
	 private void tagBarrierIDsInProcedure(TranslationUnit tu, Procedure proc) {
		    List<OmpdAnnotation> annotationList = IRTools.collectPragmas(proc, OmpdAnnotation.class, "barrier");
		    //int num_barriers = 0;		    
		    for (OmpdAnnotation annotation : annotationList) {
		    	annotation.put("barrier_id", barrier_id);
		    	barrier_id++;
		    	if(annotation.get("barrier")!=null && !((String)annotation.get("barrier")).startsWith("serial") && !((String)annotation.get("barrier")).startsWith("artificial") )	
		    		num_barriers++;
		    }
		    //prog_record.set_barriers_count(tu, proc, num_barriers);
	    }
	 
	 private void createPCFG(TranslationUnit tu, Procedure proc){
		 /* get the parallel version of control flow graph */
		 PCFGraph cfg = new PCFGraph(proc, null);
		 
		 /* sort the control flow graph */
         cfg.topologicalSort(cfg.getNodeWith("stmt", "ENTRY"));
         PrintTools.println("PCFG is created ", 0);
         /* attach information to CFG nodes */
         addInformationToCFG(tu,proc,cfg);
         
         prog_record.set_PCFGraph(tu, proc, cfg);
	 }
	 
	private void countSharedArrayAcesses(TranslationUnit tu, Procedure proc) {
		Set<Symbol> shared_arrays = OMPDTools.getSharedArrays(proc);
		TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
		PCFGraph cfg  = prog_record.get_PCFGraph(tu, proc);
        Iterator<DFANode> iter = cfg.iterator();
        Map<Symbol,Integer> DEF = new HashMap<Symbol,Integer>();
        Map<Symbol,Integer> USE = new HashMap<Symbol,Integer>();
        for(Symbol s:shared_arrays){
        	DEF.put(s, 0);
        	USE.put(s, 0);
        }
        while (iter.hasNext()) {
            DFANode node = iter.next();
            work_list.put((Integer) node.getData("top-order"), node);
        }
        for (Integer order : work_list.keySet()) {
            DFANode node = work_list.get(order);
            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
            
            if(ir instanceof ExpressionStatement){
            	Expression ac = ((ExpressionStatement)ir).getExpression();
            	if(ac instanceof AssignmentExpression)
					 ac = ((AssignmentExpression)ac).getLHS();
				    else if(ac instanceof UnaryExpression)
					 ac = ((UnaryExpression)ac).getExpression();
            	if(ac instanceof ArrayAccess && shared_arrays.contains(SymbolTools.getSymbolOf(ac))){
            		Integer tmp = DEF.get(SymbolTools.getSymbolOf(ac));
            		tmp++;
            		DEF.put(SymbolTools.getSymbolOf(ac), tmp);
            	}
            
            }
            
            if(ir instanceof ExpressionStatement){
            	Expression exp = ((ExpressionStatement)ir).getExpression();
            	if(exp instanceof AssignmentExpression)
   					 exp = ((AssignmentExpression)exp).getRHS();
   				else if(exp instanceof UnaryExpression)
   					 exp = ((UnaryExpression)exp).getExpression();
            	List<ArrayAccess> lst = IRTools.getExpressionsOfType(exp, ArrayAccess.class);
            	if(!lst.isEmpty()){
            		for(ArrayAccess ac:lst)
            			if(shared_arrays.contains(SymbolTools.getSymbolOf(ac))){
            				Integer tmp = USE.get(SymbolTools.getSymbolOf(ac));
                    		tmp++;
                    		USE.put(SymbolTools.getSymbolOf(ac), tmp);
            			}
            	}   
            }
        }
        
        for(Symbol s:shared_arrays)
        	PrintTools.println("Array "+ s.toString() + ", DEFs= " +String.format("%d,", DEF.get(s))+ ", USEs= " +String.format("%d,", USE.get(s)), 0);
	}
	 
	 private void addInformationToCFG(TranslationUnit tu, Procedure proc, DFAGraph cfg) {

         addRangeDomainToCFG(cfg);
         PrintTools.println("Integer-Value Range Analysis is performed ", 0);
         addUnkownSymbolSets(cfg);
         addExpandableSymbolSets(cfg);
         addParallelForLoopInformationToCFG(tu,proc,cfg);
         addOuterSerialLoopsInformationToCFG(cfg);
	    }
	 
/*I use RaeachAnalysis to compute RangeInfo
 *TODO: re-consider the function with account to global/private variables in each scope
 * */
	 private void addRangeDomainToCFG(DFAGraph cfg) {
		 TreeMap work_list = new TreeMap();
	     DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
	     work_list.put(entry.getData("top-order"), entry);	
	     Map<DFANode,RangeDomain> ranges_in = new HashMap<DFANode,RangeDomain>();
	     Map<DFANode,RangeDomain> ranges_out = new HashMap<DFANode,RangeDomain>();
	     while (!work_list.isEmpty()) {
	    	 DFANode node = (DFANode) work_list.remove(work_list.firstKey());
	    	 Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
	         RangeDomain rd_in = null;
	    	 for (DFANode pred : node.getPreds()) {
	    		 //RangeDomain pred_rd_out = (RangeDomain) pred.getData("range_out");
	    		 RangeDomain pred_rd_out = ranges_out.get(pred);
	    		 if(rd_in==null)
	    			 rd_in = pred_rd_out.clone();
	    		 
	    		 else if(pred_rd_out!=null && !pred_rd_out.getSymbols().isEmpty()){
	    			 DFANode temp = (DFANode) node.getData("back-edge-from");
	    			 if (temp != null && temp == pred)
	    				// this data is from a back-edge, union it with the current data
	    				 for(Symbol val:pred_rd_out.getSymbols()){
		    				 if(rd_in.getSymbols().contains(val))
		    					 rd_in.setRange(val, RangeDomain.unionRanges(rd_in.getRange(val), rd_in, pred_rd_out.getRange(val), pred_rd_out));
		    				 else
		    					 rd_in.setRange(val, pred_rd_out.getRange(val));
		    			 }
	    			 else
	    				// this is an if-else branch, thus intersect it with the current data
	    				 for(Symbol s:pred_rd_out.getSymbols())
		    				 if(rd_in.getSymbols().contains(s))
		    					 //rd_in.setRange(s, RangeDomain.intersectRanges(rd_in.getRange(s), rd_in, pred_rd_out.getRange(s), pred_rd_out));
	    			 			 rd_in.setRange(s, RangeDomain.unionRanges(rd_in.getRange(s), rd_in, pred_rd_out.getRange(s), pred_rd_out));
	    			 
	    		 }
	    	 }
	    	 if(rd_in==null)
	    		 rd_in = new RangeDomain();
	    	 
	    	if(ranges_in.get(node) == null || hasChanged(ranges_in.get(node),rd_in)){
	    		//node.putData("range_in", rd_in);
	    		ranges_in.put(node, rd_in);
	    		
	    		RangeDomain rd_local = null;
		         if(ir instanceof ForLoop){
		        	 RangeDomain tmp1 = RangeAnalysis.getRangeDomain((Statement)node.getData("ir"));
		        	 RangeDomain tmp2 = RangeAnalysis.extractRanges((Expression)((DFANode)node.getData("for-condition")).getData("ir"));
		        	 //Expression strd = (Expression)((DFANode)node.getData("for-step")).getData("ir");
		        	 int direction = OMPDTools.getLoopDirection((ForLoop)ir, rd_in);
		        	 if(direction==0)
						 Tools.exit("ERROR in addRangeDomainToCFG() in SPMDizer: Unsupported Stride Expression");
		        	 if(tmp1!=null){
		        		 rd_local = new RangeDomain();
		        		 for(Symbol s:tmp1.getSymbols()){ //there should be one symbol; index symbol 
		        			 Expression ex1 = tmp1.getRange(s);
		        			 Expression ex2 = tmp2.getRange(s);
		        			 if(direction==1)
		        				 rd_local.setRange(s, new RangeExpression(ex1.clone(),((RangeExpression)ex2).getUB().clone() ));
		        			 else
		        				 rd_local.setRange(s, new RangeExpression(((RangeExpression)ex2).getLB().clone(), ex1.clone() ));
		        		 }
		        	 }
		         }
		         else if(node.getData("tag")!=null && node.getData("tag")=="FOREXIT"){
		        	 ForLoop loop = (ForLoop) node.getData("stmt-exit");
		        	 Expression max = Symbolic.simplify(new BinaryExpression(LoopTools.getIncrementExpression(loop).clone(),BinaryOperator.ADD,LoopTools.getUpperBoundExpression(loop).clone()));
		        	 max = rd_in.substituteForward(max);
		        	 rd_local = new RangeDomain();
		        	 rd_local.setRange(LoopTools.getLoopIndexSymbol(loop), max);
		         }
		         else if(ir instanceof ExpressionStatement){
		        	 Expression ex= ((ExpressionStatement)ir).getExpression();
		        	 if(ex instanceof AssignmentExpression){
		        		 
		        		 Expression RHS = rd_in.substituteForward(((AssignmentExpression)ex).getRHS());
		        		 Expression LHS = ((AssignmentExpression)ex).getLHS().clone();
		        		 
		        		 if(((AssignmentExpression)ex).getOperator().equals(AssignmentOperator.NORMAL))
		        			 rd_local = RangeAnalysis.getRangeDomain(new ExpressionStatement(new AssignmentExpression(LHS,AssignmentOperator.NORMAL,RHS)));
		        		 else{
		        			 String stt = ((AssignmentExpression)ex).getOperator().toString();
		        			 BinaryOperator op = BinaryOperator.fromString(stt.replace("=", ""));
		        			 rd_local = RangeAnalysis.getRangeDomain(new ExpressionStatement(new AssignmentExpression(LHS,AssignmentOperator.NORMAL,new BinaryExpression(rd_in.substituteForward(LHS),op,RHS))));
		        		 }
		        	 }
		        	 else if(ex instanceof UnaryExpression){
		        		 Expression LHS = ((UnaryExpression)ex).getExpression().clone();
		        		 Expression RHS = rd_in.substituteForward(((UnaryExpression)ex).getExpression());
		        		 rd_local = RangeAnalysis.getRangeDomain(new ExpressionStatement(new AssignmentExpression(LHS,AssignmentOperator.NORMAL,new BinaryExpression(new IntegerLiteral(1),BinaryOperator.ADD,RHS))));
		        		 
		        	 }
		        	 else{
		        		 rd_local = RangeAnalysis.getRangeDomain((Statement)ir);
		        	 }
		        	 
		         }
		        	 
		         
		         if(rd_local==null || rd_local.getSymbols().isEmpty()){
		        	 //node.putData("range_out", rd_in);
		        	 ranges_out.put(node, rd_in);
		         }
		         else if(rd_in.getSymbols().isEmpty()){
		        	 //node.putData("range_out", rd_local);
		        	 ranges_out.put(node, rd_local);
		         }
		         else {
		        	 RangeDomain tmp = rd_in.clone();
		        	 for(Symbol s:rd_local.getSymbols()){
		        		 tmp.setRange(s, rd_local.getRange(s));
		        	 }
		        	 //node.putData("range_out", tmp);
		        	 ranges_out.put(node, tmp);
		         }
		         
		         for (DFANode succ : node.getSuccs()) {
	                 work_list.put(succ.getData("top-order"), succ);
	             }
	    		
	    	}
	     }
	     
	     work_list=null;
	     TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
		 Iterator<DFANode> iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	            DFANode node = node_list.get(order);
	            if(!ranges_in.get(node).getSymbols().isEmpty()){
	            	node.putData("range_in", ranges_in.get(node).clone());
	            }
	            if(!ranges_out.get(node).getSymbols().isEmpty()){
	            	node.putData("range_out", ranges_out.get(node).clone());
	            }
	     }
	     node_list=null;
	     ranges_in=null;
	     ranges_out=null;	     
	 }
	 
	 private boolean hasChanged(RangeDomain r1, RangeDomain r2){
		 if(r1.getSymbols().equals(r2.getSymbols()))
			 return false;
		 for(Symbol s:r1.getSymbols()){
			 if(!r1.getRange(s).equals(r2.getRange(s)))
				 return false;
		 }
		 return true;
	 }
	 
	 private void addUnkownSymbolSets(DFAGraph cfg){
			TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
	        Iterator<DFANode> iter = cfg.iterator();
	        while (iter.hasNext()) {
	            DFANode node = iter.next();
	            work_list.put((Integer) node.getData("top-order"), node);
	        }
	        for (Integer order : work_list.keySet()) {
	            DFANode node = work_list.get(order);
	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
	            if(ir instanceof ExpressionStatement){
	            	Expression ex= ((ExpressionStatement)ir).getExpression();
	            	Expression LHS=null;
	            	if(ex instanceof AssignmentExpression)
	            		LHS = ((AssignmentExpression)ex).getLHS();
	            	else if(ex instanceof UnaryExpression)
	            		LHS = ((UnaryExpression)ex).getExpression();
	            	else
	            		continue;
	            	RangeDomain rd = (RangeDomain) node.getData("range_out");
	            	Set<Symbol> Unknowns = new HashSet<Symbol>(); 
	            	for(Symbol s: DataFlowTools.getUseSymbol(LHS)){
	            		if(SymbolTools.isInteger(s) && SymbolTools.isScalar(s)){
	            			if(rd==null || rd.getRange(s)==null)
	            				Unknowns.add(s);
	            		}
	            	}
	            	if(!Unknowns.isEmpty())
	            		node.putData("UnknownSymbolSet", Unknowns);
	            	
	            }
	        }
		}
	 
		private void addExpandableSymbolSets(DFAGraph cfg){
			TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
	        Iterator<DFANode> iter = cfg.iterator();
	        while (iter.hasNext()) {
	            DFANode node = iter.next();
	            work_list.put((Integer) node.getData("top-order"), node);
	        }
	        for (Integer order : work_list.keySet()) {
	            DFANode node = work_list.get(order);
	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
	            if(ir instanceof ForLoop){
	            	Set<Symbol> Expand = new HashSet<Symbol> ();
	            	Expand.add(LoopTools.getLoopIndexSymbol((ForLoop)ir));
	            	((DFANode)node.getData("for-condition")).putData("ExpandableSymbolSet", Expand);
	            	((DFANode)node.getData("for-step")).putData("ExpandableSymbolSet", Expand);
	            }
	            else if (node.getData("tag") != null && node.getData("tag").equals("barrier")){
	            	String type = (String) node.getData("type");
	            	if(type.equals("serial_loop_up")){
	            		Set<Symbol> Expand = new HashSet<Symbol> ();
		            	Expand.add(LoopTools.getLoopIndexSymbol((ForLoop)node.getData("source")));
		            	node.putData("ExpandableSymbolSet", Expand);
	            	}
	            	else if(type.equals("serial_loop_down")){
	            		Set<Symbol> Expand = new HashSet<Symbol> ();
		            	Expand.add(LoopTools.getLoopIndexSymbol((ForLoop)node.getData("source")));
		            	node.putData("ExpandableSymbolSet", Expand);
	            	}
	            }
	        }
		}
 		private void addParallelForLoopInformationToCFG(TranslationUnit tu, Procedure proc, DFAGraph cfg) {
            TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
	        Iterator<DFANode> iter = cfg.iterator();
	        while (iter.hasNext()) {
	            DFANode node = iter.next();
	            work_list.put((Integer) node.getData("top-order"), node);
	        }

	        OMPDParallelForLoop current_work_sharing = null;
	        
	        for (Integer order : work_list.keySet()) {
	            DFANode node = work_list.get(order);
	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));

                //attach the outer work-sharing construct (currently, only omp for) information
	            if(ir instanceof ForLoop){
	            	OmpdAnnotation annot = ((ForLoop) ir).getAnnotation(OmpdAnnotation.class, "for");
	            	if(annot != null){
	            		OMPDParallelForLoop pfor = prog_record.get_loop_record(tu, proc, annot);
	            		pfor.set_RangeInfo((RangeDomain)node.getData("range_out"));
	            		current_work_sharing = pfor;
	            	}
	            }
	           if(current_work_sharing != null) if(node.getData("tag") != null) if(node.getData("tag").equals("FOREXIT")){
	        	   ForLoop loop = (ForLoop) node.getData("stmt-exit");
	        	   if(loop.equals(current_work_sharing.get_Forloop()))
	        		   current_work_sharing = null;
	           }
	           if(current_work_sharing!=null)
	            node.putData("inside_pfor", current_work_sharing);
	        }
	    	
	    }

 		private void addOuterSerialLoopsInformationToCFG(DFAGraph cfg){
 			Map<ForLoop,DFANode> before = new HashMap<ForLoop,DFANode>();
 			Map<ForLoop,DFANode> after = new HashMap<ForLoop,DFANode>();
 			Map<ForLoop,DFANode> up = new HashMap<ForLoop,DFANode>();
 			Map<ForLoop,DFANode> down = new HashMap<ForLoop,DFANode>();
 			TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
	        Iterator<DFANode> iter = cfg.iterator();
	        while (iter.hasNext()) {
	            DFANode node = iter.next();
	            work_list.put((Integer) node.getData("top-order"), node);
	        }
	        for (Integer order : work_list.keySet()) {
	            DFANode node = work_list.get(order);
	            if(OMPDTools.isBarrierNodeButNotFromSerialToParallel(node) ){
	            	String type = (String) node.getData("type");
	            	if(type.equals("serial_loop_before")){
	            		before.put((ForLoop)node.getData("source"), node);
	            	}
	            	else if(type.equals("serial_loop_after")){
	            		after.put((ForLoop)node.getData("source"), node);
	            	}
	            	else if(type.equals("serial_loop_up")){
	            		up.put((ForLoop)node.getData("source"), node);
	            	}
	            	else if(type.equals("serial_loop_down")){
	            		down.put((ForLoop)node.getData("source"), node);
	            	}
	            }
	        }
	        work_list=null;
	        iter=null;
	        assert(before.keySet().size()==after.keySet().size());
	        assert(before.keySet().size()==up.keySet().size());
	        assert(before.keySet().size()==down.keySet().size());
	        for(ForLoop lp: before.keySet()){
	        	DFANode bfr = before.get(lp);
	        	DFANode aftr = after.get(lp);
	        	DFANode upp = up.get(lp);
	        	DFANode dwn = down.get(lp);
	        	bfr.putData("serial_loop_after", aftr);
	        	bfr.putData("serial_loop_up", upp);
	        	bfr.putData("serial_loop_down", dwn);
	        	aftr.putData("serial_loop_before", bfr);
	        	aftr.putData("serial_loop_up", upp);
	        	aftr.putData("serial_loop_down", dwn);
	        	upp.putData("serial_loop_before", bfr);
	        	upp.putData("serial_loop_down", dwn);
	        	upp.putData("serial_loop_after", aftr);
	        	dwn.putData("serial_loop_before", bfr);
	        	dwn.putData("serial_loop_up", upp);
	        	dwn.putData("serial_loop_before", bfr);
	        }
 		}
 		
 	/**A loop is repetitive if its iteration space is repetitive**/	
 		private void DetermineRepetitiveLoops(TranslationUnit tu, Procedure proc){
 			Set<Symbol> shared_arrays = OMPDTools.getSharedArrays(proc);
 			DFAGraph cfg = prog_record.get_PCFGraph(tu, proc);
 			 TreeMap<Integer, DFANode> work_list = new TreeMap<Integer, DFANode>();
 	        Iterator<DFANode> iter = cfg.iterator();
 	        while (iter.hasNext()) {
 	            DFANode node = iter.next();
 	            work_list.put((Integer) node.getData("top-order"), node);
 	        }
 	        
 	        for (Integer order : work_list.keySet()) {
 	            DFANode node = work_list.get(order);
 	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));

                 //attach the outer work-sharing construct (currently, only omp for) information
 	            if(ir instanceof ForLoop){
 	            	OmpdAnnotation annot = ((ForLoop) ir).getAnnotation(OmpdAnnotation.class, "for");
 	            	if(annot != null){
 	            		OMPDParallelForLoop pfor = prog_record.get_loop_record(tu, proc, annot);
 	            		RangeDomain rd = (RangeDomain)node.getData("range_out");
 	            		Symbol OuterSerialLoopIndex = LoopTools.getLoopIndexSymbol(pfor.get_outer_serial_loop());
 	            		Expression range = rd.getRange(LoopTools.getLoopIndexSymbol((ForLoop) ir));
 	            		range = rd.substituteForward(range);
 	            		boolean non_repetitive = false;
 	            		if(SymbolTools.getAccessedSymbols(range).contains(OuterSerialLoopIndex)
 	            				|| SymbolTools.getAccessedSymbols(LoopTools.getIncrementExpression((ForLoop) ir)).contains(OuterSerialLoopIndex)){
 	            			pfor.MakeNonRepetitive();
 	            			foundNonRepetitiveLoop = true;
 	            			non_repetitive= true;
 	            		}
 	            		else{
 	            			List<ArrayAccess> acc_set =  IRTools.getExpressionsOfType((ForLoop) ir, ArrayAccess.class);
 	 	    			    if(!acc_set.isEmpty()){
 	 	    			    	ArrayList<ArrayAccess> uniq=new ArrayList<ArrayAccess>();
 	 	    	        		for(ArrayAccess s:acc_set)
 	 	    	        			if(!uniq.contains(s) && shared_arrays.contains(SymbolTools.getSymbolOf(s)))
 	 	    	        				uniq.add(s);
 	 	    	        		for(ArrayAccess s: uniq)
 	 	    	        			if(SymbolTools.getAccessedSymbols(s).contains(OuterSerialLoopIndex)){
 	 	    	        				//pfor.MakeNonRepetitive();
 	 	    	        				foundNonRepetitiveLoop = true;
 	 	    	        				//non_repetitive = true;
 	 	    	        			}
 	 	    			    }
 	            		}
 	    			    if(!non_repetitive)
 	    			    	pfor.MakeRepetitive();
 	            	}
 	            }
 	           
 	        }
	        
 		}
 	
}
