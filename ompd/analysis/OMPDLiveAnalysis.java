package ompd.analysis;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import ompd.hir.OMPDParallelForLoop;
import ompd.hir.OMPDTools;
import ompd.hir.SectionSet;
import ompd.hir.SectionSet.ELEMENT;
import ompd.hir.SectionSet.MAP;
import ompd.hir.SectionSet.RSD;
import ompd.transforms.ProgramRecord;
import cetus.analysis.DFANode;
import cetus.analysis.LoopTools;
import cetus.analysis.RangeDomain;
import cetus.exec.Driver;
import cetus.hir.*;

public class OMPDLiveAnalysis {
	
	private PCFGraph cfg;
	private Set<Symbol> shared_vars, shared_arrays;
	private ProgramRecord prog_record;
	private DFANode entry;
	private DFANode exit;
	private Map<DFANode,SectionSet.MAP> USESetsofStatements;
	private Map<DFANode,SectionSet.MAP> DEFALLSetsofStatements;
	private Map<DFANode,SectionSet.MAP> KILLSetsofStatements;
	private Map< DFANode, Set<DFANode> > barrier_predecssors;
	private Map< DFANode, Set<DFANode> > barrier_successors;
	private Map<DFANode,SectionSet.MAP> GUSEin;
	private Map<DFANode,SectionSet.MAP> GUSEout;
    
    private boolean turnoffERSD;
    private boolean turnoffsubtract;
	
	public OMPDLiveAnalysis(ProgramRecord rcd){
		this.prog_record=rcd;
		if(Driver.getOptionValue("turn-off-ersd")!=null)
			turnoffERSD = true;
		else
			turnoffERSD = false;
		if(Driver.getOptionValue("turn-off-subtraction")!=null)
			turnoffsubtract = true;
		else
			turnoffsubtract = false;
	}
	
	public void start(){
		for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	cfg = prog_record.get_PCFGraph(tu, proc);
            	//range_map = prog_record.get_range_map(tu, proc);
            	shared_arrays = OMPDTools.getSharedArrays(proc);
            	shared_vars = OMPDTools.getSharedVariables(proc);
            	performLiveAnalysis();
            }
		}
	}
	
	private void performLiveAnalysis(){
		entry = cfg.getNodeWith("stmt", "ENTRY");
		List<DFANode> exit_nodes = cfg.getExitNodes();
        if (exit_nodes.size() > 1) {
            PrintTools.println("Not Allowed: multiple exits in the program", 2);
            System.exit(0);
        }
        exit = exit_nodes.get(0);
		barrier_predecssors = new HashMap< DFANode, Set<DFANode> > ();
	    barrier_successors = new HashMap< DFANode, Set<DFANode> > ();
	    computeBarriersCFG(); // create reduced PCG that has only barrier nodes
	    DEFALLSetsofStatements = new HashMap<DFANode,SectionSet.MAP>();
		KILLSetsofStatements = new HashMap<DFANode,SectionSet.MAP>();
		computeDEFALLSetsofStatements(); // compute serial DEF set (i.e., kill sets) for each node, independently, in the PCFG
		computeKILLSetsofSPMDBlocks(); // compute KILL sets for each SPMD block
		DEFALLSetsofStatements=null; 
				
		// compute local USE sets
		USESetsofStatements = new HashMap<DFANode,SectionSet.MAP>();
		computeUSESetsofStatements(); //compute read set for each node, independently, in the PCFG
		computeGENSetsofSPMDBlocks(); // compute local read GEN sets of SPMD blocks
		
		if(Driver.getOptionValue("no-global-use")==null){ 
			GUSEin = new HashMap<DFANode,SectionSet.MAP>();
			GUSEout = new HashMap<DFANode,SectionSet.MAP>();
			
			if(Driver.getOptionValue("use-explicit-partitioning")!=null)
				computeGlobalUSESetsEXP( ); // user has activate use-explicit-partitioning flag 
			else
				computeGlobalUSESets( ); // default -- use pi operators
			
			AttachToNodes("USEGlobal",GUSEout);
			GUSEin=null;
			GUSEout=null;	
		}
		KILLSetsofStatements=null;
		USESetsofStatements=null;
		barrier_predecssors=null;
		barrier_successors=null;
	}

	/** computes write sets of each statement*/
	private void computeDEFALLSetsofStatements(){
		 TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
		 Iterator<DFANode> iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	            DFANode node = node_list.get(order);
	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
	            if(ir instanceof ExpressionStatement){
	            	Expression ac = ((ExpressionStatement)ir).getExpression();
	            	if(ac instanceof AssignmentExpression)
   					 ac = ((AssignmentExpression)ac).getLHS();
   				    else if(ac instanceof UnaryExpression)
   					 ac = ((UnaryExpression)ac).getExpression();
	            	if(ac instanceof ArrayAccess && shared_arrays.contains(SymbolTools.getSymbolOf(ac))){
	            		SectionSet.SECTION DEF = 
	            			getSection((ArrayAccess)ac,
	            					(RangeDomain) node.getData("range_out"),
	            					(Set<Symbol>) node.getData("ExpandableSymbolSet"),
	            			        null); 
	            		//node.putData("DEF", new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(DEF)));
	            		DEFALLSetsofStatements.put(node, new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(DEF)));
	            	}
	            	else{
	            		//TODO: handle scalars
	            		//node.putData("DEF", null);
	            	}
	            
	            }
	            else{
	            	//node.putData("DEF", null);
	            }   	      
	     }
	     node_list=null;
	     iter=null;
	}
	
	/** computes write sets of each SPMD block **/
	private void computeKILLSetsofSPMDBlocks(){
		 TreeMap work_list = new TreeMap();
		 // Enter the entry node in the work_list
	     Map<DFANode,SectionSet.MAP> sections_in = new HashMap<DFANode,SectionSet.MAP>();
	     Map<DFANode,SectionSet.MAP> sections_out = new HashMap<DFANode,SectionSet.MAP>();
	     //entry.putData("KILL_in", new SectionSet.MAP());
	     work_list.put(entry.getData("top-order"), entry);
		  // Do iterative steps to compute KILL_in & KILL_out
		     while (!work_list.isEmpty()) {
		    	 DFANode node = (DFANode) work_list.remove(work_list.firstKey());
		         SectionSet.MAP KILL_in = null;
		         
		         for (DFANode pred : node.getPreds()) {
		        	 //SectionSet.MAP pred_KILL_out = (SectionSet.MAP) pred.getData("KILL_out");
		        	 SectionSet.MAP pred_KILL_out = sections_out.get(pred);
		        	 
		        	 if (KILL_in == null) {
		        		 KILL_in = (SectionSet.MAP) pred_KILL_out.clone();
		                } else {
		                    DFANode temp = (DFANode) node.getData("back-edge-from");
		                    if (temp != null && temp == pred) {
		                        // this data is from a back-edge, union it with the current data
		                    	KILL_in = KILL_in.unionWith(pred_KILL_out, (RangeDomain) node.getData("range_in"));
		                    } else {
		                        // this is an if-else branch, thus intersect it with the current data
		                    	KILL_in = KILL_in.intersectWith(pred_KILL_out, (RangeDomain) node.getData("range_in"));
		                    }
		                }
		         }
		         
		         // previous must_def_in
		         //SectionSet.MAP p_KILL_in = (SectionSet.MAP) node.getData("KILL_in");
		         SectionSet.MAP p_KILL_in = sections_in.get(node);
	             if(p_KILL_in==null || p_KILL_in.hasChanged(KILL_in, (RangeDomain) node.getData("range_in"))){
	            	 //node.putData("KILL_in", KILL_in);
	            	 sections_in.put(node, KILL_in);

	                 
	                 if(isBarrierNode(node)){
	                	 //node.putData("KILL_out", new SectionSet.MAP() );
	                	 sections_out.put(node, new SectionSet.MAP());
	                 }
	                 else{
	                	 if(KILL_in == null){
	                		 if(/*(node.getData("DEF"))*/DEFALLSetsofStatements.get(node)==null){
	                			 //node.putData("KILL_out", new SectionSet.MAP() );
	                			 sections_out.put(node, new SectionSet.MAP());
	                		 }
	                		 else{
	                			 SectionSet.MAP tmp = DEFALLSetsofStatements.get(node).clone();
	                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
	                			 //node.putData("KILL_out", tmp );
	                			 sections_out.put(node, tmp);
	                		 }
	                     }
	                	 else {
	                		 //OMPDParallelForLoop pfor =(OMPDParallelForLoop)node.getData("inside_pfor");
	                		 if(/*node.getData("DEF")*/DEFALLSetsofStatements.get(node)==null){
	                			 SectionSet.MAP tmp = (SectionSet.MAP)KILL_in.clone();
	                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
	                			 //node.putData("KILL_out", tmp);
	                			 sections_out.put(node, tmp);
	                		 }
	                		 else{
	                			 SectionSet.MAP DEF = DEFALLSetsofStatements.get(node).clone();
	                			 SectionSet.MAP tmp = KILL_in.unionWith(DEF, (RangeDomain) node.getData("range_out"));
	                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
	                			 //node.putData("KILL_out", tmp );
	                			 sections_out.put(node, tmp);
	                		 }
	                	 }
	                 }
	                 
	                 for (DFANode succ : node.getSuccs()) {
	                	 DFANode temp = (DFANode) succ.getData("back-edge-from");
	                	 if(temp!=null && temp.equals(node))
	                		 continue;
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
		            if(order!=0){
		            	if(!sections_out.get(node).isEmpty())
		            		KILLSetsofStatements.put(node, sections_out.get(node).clone());
		            }
		     }
		     sections_out=null;
		     node_list=null;
		     
		     AttachToNodes("KILL_in",sections_in);
		     sections_in=null;
		     
	}
	
/** computes read sets of each statement. Those sets represent GEN sets of Local USE analysis*/
	private void computeUSESetsofStatements(){
		TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
		 Iterator<DFANode> iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	            DFANode node = node_list.get(order);
	            Object ir = node.getData(Arrays.asList("super-entry", "stmt"));
	            if(ir instanceof ExpressionStatement){
	            	Expression exp = ((ExpressionStatement)ir).getExpression();
	            	if(exp instanceof AssignmentExpression)
	   					 exp = ((AssignmentExpression)exp).getRHS();
	   				else if(exp instanceof UnaryExpression)
	   					 exp = ((UnaryExpression)exp).getExpression();
	            	List<ArrayAccess> lst = IRTools.getExpressionsOfType(exp, ArrayAccess.class);
	            	if(!lst.isEmpty()){
	            		ArrayList<ArrayAccess> uniq=new ArrayList<ArrayAccess>();
	            		for(ArrayAccess s:lst){
	            			if(!uniq.contains(s) && shared_arrays.contains(SymbolTools.getSymbolOf(s))){
	            				uniq.add(s);
	            			}
	            		}
	            		if(uniq.isEmpty())
	            			continue;
	            		SectionSet.MAP set = new SectionSet.MAP();
	            		for(ArrayAccess ac:uniq){
	            			SectionSet.SECTION USE = 
		            			getSection((ArrayAccess)ac,
		            					(RangeDomain) node.getData("range_out"),
		            					(Set<Symbol>) node.getData("ExpandableSymbolSet"),
		            			        (OMPDParallelForLoop)node.getData("inside_pfor"));
	            			if(Driver.getOptionValue("disable-varying-gen")!=null || prog_record.IsRepetitiveProgram()==false)
	            				set = set.unionWith(new SectionSet.MAP(SymbolTools.getSymbolOf(ac), remove_varying_variables(USE,(ArrayAccess)ac,(RangeDomain) node.getData("range_out"))), (RangeDomain) node.getData("range_out"));
	            			else
	            				set = set.unionWith(new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(USE)), (RangeDomain) node.getData("range_out"));
	            		}
	            		//node.putData("USE", set);
	            		USESetsofStatements.put(node, set);
	            	}
	            	else{
		            	//node.putData("USE", null);
		            }   
	            }
	            else if(ir instanceof IfStatement){
	            	Expression cond = ((IfStatement)ir).getControlExpression();
	            	List<ArrayAccess> lst = IRTools.getExpressionsOfType(cond, ArrayAccess.class);
	            	if(!lst.isEmpty()){
	            		ArrayList<ArrayAccess> uniq=new ArrayList<ArrayAccess>();
	            		for(ArrayAccess s:lst){
	            			if(!uniq.contains(s) && shared_arrays.contains(SymbolTools.getSymbolOf(s))){
	            				uniq.add(s);
	            			}
	            		}
	            		if(uniq.isEmpty())
	            			continue;
	            		SectionSet.MAP set = new SectionSet.MAP();
	            		for(ArrayAccess ac:uniq){
	            			SectionSet.SECTION USE = 
		            			getSection((ArrayAccess)ac,
		            					(RangeDomain) node.getData("range_out"),
		            					(Set<Symbol>) node.getData("ExpandableSymbolSet"),
		            			        (OMPDParallelForLoop)node.getData("inside_pfor"));
	            			set = set.unionWith(new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(USE)), (RangeDomain) node.getData("range_out"));
	            		}
	            		//node.putData("USE", set);
	            		USESetsofStatements.put(node, set);
	            	}
	            }
	            else if(ir instanceof ForLoop){
	            	Expression max = LoopTools.getUpperBoundExpression((ForLoop)ir);
	            	Expression step = LoopTools.getIncrementExpression((ForLoop)ir);
	            	Expression min = LoopTools.getLowerBoundExpression((ForLoop)ir);
	            	List<ArrayAccess> lst1 = IRTools.getExpressionsOfType(max, ArrayAccess.class);
	            	List<ArrayAccess> lst2 = IRTools.getExpressionsOfType(min, ArrayAccess.class);
	            	List<ArrayAccess> lst3 = IRTools.getExpressionsOfType(step, ArrayAccess.class);
	            	List<ArrayAccess> lst = new LinkedList<ArrayAccess>();
	            	lst.addAll(lst1); lst.addAll(lst2); lst.addAll(lst3);
	            	if(!lst.isEmpty()){
	            		ArrayList<ArrayAccess> uniq=new ArrayList<ArrayAccess>();
	            		for(ArrayAccess s:lst){
	            			if(!uniq.contains(s) && shared_arrays.contains(SymbolTools.getSymbolOf(s))){
	            				uniq.add(s);
	            			}
	            		}
	            		if(uniq.isEmpty())
	            			continue;
	            		SectionSet.MAP set = new SectionSet.MAP();
	            		for(ArrayAccess ac:uniq){
	            			SectionSet.SECTION USE = 
		            			getSection((ArrayAccess)ac,
		            					(RangeDomain) node.getData("range_out"),
		            					(Set<Symbol>) node.getData("ExpandableSymbolSet"),
		            			        (OMPDParallelForLoop)node.getData("inside_pfor"));
	            			set = set.unionWith(new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(USE)), (RangeDomain) node.getData("range_out"));
	            		}
	            		//node.putData("USE", set);
	            		USESetsofStatements.put(node, set);
	            	}
	            	
	            }
	            else{
	            	//node.putData("USE", null);
	            }   
	     }
	}
	
	/** computes upwardly exposed local USE sets within SPMD blocks. Those sets represent GEN sets of Global USE analysis*/
	private void computeGENSetsofSPMDBlocks(){
		int count=0;
		TreeMap<Object, DFANode> work_list = new TreeMap<Object, DFANode>();
		/* Enter the exit node in the work_list */
		work_list.put(exit.getData("top-order"), exit);
        
        Map<DFANode,SectionSet.MAP> sections_in = new HashMap<DFANode,SectionSet.MAP>();
	    Map<DFANode,SectionSet.MAP> sections_out = new HashMap<DFANode,SectionSet.MAP>();
        
        /* Do iterative steps */
        while (!work_list.isEmpty()) {
            if (count++ > (cfg.size() * 10)) {
                PrintTools.println(cfg.toDot("tag,ir,ueuse", 3), 0);
                PrintTools.println("cfg size = " + cfg.size(), 0);
                Tools.exit("[localAnalysis] infinite loop!");
            }

            DFANode node = work_list.remove(work_list.lastKey());
            SectionSet.MAP GEN_out = new SectionSet.MAP();
            
            
            
            /* calculate the current live_out to check if there is any change */
            for (DFANode succ : node.getSuccs()) {
            	//GEN_out = GEN_out.unionWith((SectionSet.MAP) succ.getData("GEN_in"), (RangeDomain) node.getData("range_in"));
            	GEN_out = GEN_out.unionWith( sections_in.get(succ) , (RangeDomain) node.getData("range_in"));
            }
            
            /* retrieve previous live_out */
            //SectionSet.MAP p_GEN_out = (SectionSet.MAP) node.getData("GEN_out");
            SectionSet.MAP p_GEN_out = sections_out.get(node);
            if(p_GEN_out==null || p_GEN_out.hasChanged(GEN_out, (RangeDomain) node.getData("range_in"))){
            	/* since live_out has been changed, we update it. */
            	//node.putData("GEN_out", GEN_out);
            	sections_out.put(node, GEN_out);
            	
            	if (OMPDTools.isBarrierNodeButNotFromSerialToParallel(node)){
            		//node.putData("GEN_in", new SectionSet.MAP());
            		//GEN_out.optimize((RangeDomain) node.getData("range_out"));
            		sections_in.put(node, new SectionSet.MAP());
            	}
            	else{
            		/* compute Upward-Exposed-Use set = LocalUEUse + (Live - DEF) */
                	//SectionSet.MAP GEN = (SectionSet.MAP) node.getData("USE");
                	SectionSet.MAP GEN = USESetsofStatements.get(node);
                	//SectionSet.MAP KILL = (SectionSet.MAP) node.getData("KILL_out");
                	SectionSet.MAP KILL = KILLSetsofStatements.get(node);
                	
                	if(GEN==null){
                		SectionSet.MAP tmp;
                		if(turnoffsubtract)
                			tmp = GEN_out.clone();
                		else
                			tmp = GEN_out.subtractFrom(KILL, (RangeDomain) node.getData("range_out"), false);

                		if(!tmp.isEmpty()){
                			tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                			tmp.RemoveUnknwonSymbols((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("UnknownSymbolSet"));
                		}                		
                		//node.putData("GEN_in", tmp);
                		sections_in.put(node, tmp);
                	}
                	else{
                		SectionSet.MAP tmp0;
                		if(turnoffsubtract)
                			tmp0 = GEN_out;
                		else
                		    tmp0 = GEN_out.subtractFrom(KILL, (RangeDomain) node.getData("range_out"), false);
                		SectionSet.MAP tmp = tmp0.unionWith(GEN, (RangeDomain) node.getData("range_out"));
                		if(!tmp.isEmpty())
                			tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                		//node.putData("GEN_in", tmp);
                		sections_in.put(node, tmp);
                	}
            	}
            	/*for (DFANode pred : node.getPreds())
                    work_list.put(pred.getData("top-order"), pred);*/
            	DFANode temp = (DFANode) node.getData("back-edge-from");
            	for (DFANode pred : node.getPreds()) {
            			if(temp!=null && temp.equals(pred))
            				continue;
               	    work_list.put(pred.getData("top-order"), pred);
                }
            	
            }
        }
        
         work_list=null;
         sections_in=null;
         entry.putData("USElocal", sections_out.get(entry).clone() );
         exit.putData("USElocal", sections_out.get(exit).clone() );
         AttachToNodes("USElocal",sections_out);
	     sections_out=null;
	     
	}
	
	private void computeGlobalUSESets(){
		 TreeMap<Object, DFANode> work_list = new TreeMap<Object, DFANode>();
		 work_list.put(exit.getData("top-order"), exit);
		 int count=0; 
		 while (!work_list.isEmpty()) {
	            if (count++ > (cfg.size() * 10)) {
	                PrintTools.println(cfg.toDot("tag,ir,ueuse", 3), 0);
	                PrintTools.println("cfg size = " + cfg.size(), 0);
	                Tools.exit("[GlobalAnalysis] infinite loop!");
	            }
	            DFANode node = work_list.remove(work_list.lastKey());
	            RangeDomain rd = (RangeDomain) node.getData("range_out");
	            SectionSet.MAP out = new SectionSet.MAP();
	            for (DFANode succ : barrier_successors.get(node) ) 
 	            		out = out.unionWith( GUSEin.get(succ) , rd);
	            
	           SectionSet.MAP p_out = GUSEout.get(node);	           
	            if(p_out==null || p_out.hasChanged(out, rd)){
	            	GUSEout.put(node, out); 
	            	SectionSet.MAP GEN,KILL,survived,in;
	            	 GEN = new SectionSet.MAP();
         			 for (DFANode pred : barrier_predecssors.get(node))
         				GEN = GEN.unionWith((SectionSet.MAP) pred.getData("USElocal"), rd);
		            KILL = (SectionSet.MAP) node.getData("KILL_in");
		            	 if(turnoffsubtract)
		            			survived = out;
		            		else
		            			survived = out.subtractFrom( KILL , rd, !turnoffERSD);
		             	 in = GEN.unionWith(survived, rd);
		             	if(!in.isEmpty())
		             		in.substituteKnowns(rd);
		             	
		             	GUSEin.put(node, in);
		             	for (DFANode pred : barrier_predecssors.get(node)){
		            		if(!pred.equals(entry))
		            			work_list.put(pred.getData("top-order"), pred);
		            	}
	            }
	     }
	     work_list=null;

	}
	
	/** use this when user activates "use-explicit-partitioning" flag*/
	private void computeGlobalUSESetsEXP(){
		 TreeMap<Object, DFANode> work_list = new TreeMap<Object, DFANode>();
		 work_list.put(exit.getData("top-order"), exit);
		 int count=0;

		 while (!work_list.isEmpty()) {
	            if (count++ > (cfg.size() * 10)) {
	                PrintTools.println(cfg.toDot("tag,ir,ueuse", 3), 0);
	                PrintTools.println("cfg size = " + cfg.size(), 0);
	                Tools.exit("[GlobalAnalysis] infinite loop!");
	            }
	            DFANode node = work_list.remove(work_list.lastKey());
	            RangeDomain rd = (RangeDomain) node.getData("range_out");
	            SectionSet.MAP out = new SectionSet.MAP();
	            for (DFANode succ : barrier_successors.get(node) ) 
 	            		out = out.unionWith_xp( GUSEin.get(succ) , rd);
	            
	           SectionSet.MAP p_out = GUSEout.get(node);
	            if(p_out==null || p_out.hasChanged(out, rd)){
	            	GUSEout.put(node, out); 
	            	SectionSet.MAP GEN,KILL,survived,in;
	            	 GEN = new SectionSet.MAP();
        			 for (DFANode pred : barrier_predecssors.get(node))
        				GEN = GEN.unionWith_xp((SectionSet.MAP) pred.getData("USElocal"), rd);
		            	 KILL = (SectionSet.MAP) node.getData("KILL_in");
		            	 if(turnoffsubtract)
		            			survived = out;
		            		else
		            			survived = out.subtractFrom_xp( KILL , rd, !turnoffERSD);
		             	 in = GEN.unionWith_xp(survived, rd);
		             	if(!in.isEmpty())
		             		in.substituteKnowns_xp(rd);
		             	
		             	GUSEin.put(node, in);
		             	for (DFANode pred : barrier_predecssors.get(node)){
		            		if(!pred.equals(entry))
		            			work_list.put(pred.getData("top-order"), pred);
		            	}
	            }
	     }
	     work_list=null;
	     
	     /*merge right terms as much as possible in ERSD expressions**/
	     if(!turnoffERSD){
	    	 TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
			 Iterator<DFANode> iter = cfg.iterator();
		     while (iter.hasNext()) {
		            DFANode node = iter.next();
		            node_list.put((Integer) node.getData("top-order"), node);
		     }
		     for (Integer order : node_list.keySet()) {
		            DFANode node = node_list.get(order);
		            if(isBarrierNode(node)){
		            	SectionSet.MAP use = GUSEout.get(node);
		            	if(use==null || use.isEmpty())
		            		continue;
		            	RangeDomain rd = (RangeDomain) node.getData("range_out");
			            for(Symbol arr: use.getArrays())
			            	for(SectionSet.SECTION e: use.getSectionsofArray(arr)){
			            		if(e.isERSD()){
			            			if(((SectionSet.ERSD)e).size()==2)
			            				continue;
			            			SectionSet rights = new SectionSet();
			            			for(int i=1;i<((SectionSet.ERSD)e).size();i++){
			            				((SectionSet.ERSD)e).get(i).Serialize();
			            				rights.add(((SectionSet.ERSD)e).get(i),rd);
			            			}
			            			
			            			while(true){
			            				((SectionSet.ERSD)e).remove(1);
			            				if(((SectionSet.ERSD)e).size()==1) break;
			            			}
			            			for(SectionSet.SECTION ss: rights)
			            				((SectionSet.ERSD)e).add((SectionSet.RSD)ss);
			            		}
			            	}
		            }
		     }
		     node_list=null;
		     iter=null;
	     }	     
	     
	}
	
	private void AttachToNodes(String key, Map<DFANode,SectionSet.MAP> info){
		TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
	     Iterator<DFANode>  iter = cfg.iterator();
	     while (iter.hasNext()) {
	            DFANode node = iter.next();
	            node_list.put((Integer) node.getData("top-order"), node);
	     }
	     for (Integer order : node_list.keySet()) {
	            DFANode node = node_list.get(order);
	            if(OMPDTools.isBarrierNodeButNotFromSerialToParallel(node)  ){
		    		 node.putData(key, info.get(node).clone());
		    	 }
	     }
	     node_list = null;
	     iter = null;   
	}
	
	private void computeBarriersCFG(){
		     
		     TreeMap<Integer, DFANode> node_list = new TreeMap<Integer, DFANode>();
			 Iterator<DFANode> iter = cfg.iterator();
		     while (iter.hasNext()) {
		            DFANode node = iter.next();
		            node_list.put((Integer) node.getData("top-order"), node);
		     }
		     for (Integer order : node_list.keySet()) {
		            DFANode node = node_list.get(order);
		            if(node.equals(entry) || OMPDTools.isBarrierNodeButNotFromSerialToParallel(node) || node.equals(exit) ){
			    		 barrier_successors.put( node, findSuccBarriers(node) );
				    	 barrier_predecssors.put( node, findPredBarriers(node) ); 
			    	 }
		     }
		     node_list = null;
		     iter = null;
	}
	
	
	private void findSuccBarriers_(DFANode node, Set<DFANode> result, Set<DFANode> visitedNodes) {
	        if (node == null) {
	            return;
	        }

	        if (visitedNodes.contains(node)) {
	            return;
	        }

	        //PrintTools.println("findSuccBarriers_() : node = " + node, 0);

	        visitedNodes.add(node);

	        if (node.equals(entry) || OMPDTools.isBarrierNodeButNotFromSerialToParallel(node) || node.equals(exit)) {
	            result.add(node);
	        }
	        else {
	            for (DFANode succ : node.getSuccs()) {
	                findSuccBarriers_(succ, result, visitedNodes);
	            }
	        }
	    }

	    private Set<DFANode> findSuccBarriers(DFANode node) {
	        Set<DFANode> resultNodes = new HashSet<DFANode>();
	        Set<DFANode> visitedNodes = new HashSet<DFANode>();
	        visitedNodes.add(node);

	        //PrintTools.println("findSuccBarriers() node = " + node, 0);

	        for (DFANode succ : node.getSuccs()) {
	            findSuccBarriers_(succ, resultNodes, visitedNodes);
	        }
	        return resultNodes;
	    }

	    private void findPredBarriers_(DFANode node, Set<DFANode> result, Set<DFANode> visitedNodes) {
	        if (node == null) {
	            return;
	        }

	        if (visitedNodes.contains(node)) {
	            return;
	        }

	        visitedNodes.add(node);

	        if (node.equals(entry) || OMPDTools.isBarrierNodeButNotFromSerialToParallel(node) || node.equals(exit)) {
	            result.add(node);
	        }
	        else {
	            for (DFANode pred : node.getPreds()) {
	                findPredBarriers_(pred, result, visitedNodes);
	            }
	        }
	    }

	    private Set<DFANode> findPredBarriers(DFANode node) {
	        Set<DFANode> resultNodes = new HashSet<DFANode>();
	        Set<DFANode> visitedNodes = new HashSet<DFANode>();
	        visitedNodes.add(node);

	        for (DFANode pred : node.getPreds()) {
	            findPredBarriers_(pred, resultNodes, visitedNodes);
	        }
	        return resultNodes;
	    }
	
	private SectionSet.SECTION getSection(ArrayAccess ar,RangeDomain rd, Set<Symbol> Expand, OMPDParallelForLoop pfor){
	//	ArrayAccess ar = (ArrayAccess) rd.substituteForward(expr);
		SectionSet.RSD USE= null;
		if(pfor != null)
			USE = new SectionSet.RSD(ar,rd,Expand,pfor);
		else
			USE = new SectionSet.RSD(ar,rd,Expand);
		USE.set_FullSized((ArraySpecifier)SymbolTools.getSymbolOf(ar).getArraySpecifiers().get(0));
		return USE; 
		
	}
	
	private SectionSet remove_varying_variables(SectionSet.SECTION sec,ArrayAccess ar, RangeDomain rd){
		ForLoop forloop=IRTools.getAncestorOfType(ar.getStatement(), ForLoop.class);
		Set<Symbol> smbls =DataFlowTools.getUseSymbol(ar);
		if(smbls.isEmpty() || forloop==null)
			return new SectionSet(sec);
		SectionSet set = new SectionSet(sec);
		while(forloop!=null){
			if(smbls.contains(LoopTools.getLoopIndexSymbol(forloop))){
				Set<Symbol> Expand = new HashSet<Symbol>();
				Expand.add(LoopTools.getLoopIndexSymbol(forloop));
				for(SectionSet.SECTION e: set)
					if(e.isParallel() && !e.get_pfor().get_parallel_loop_index().equals(LoopTools.getLoopIndexSymbol(forloop)) && ((SectionSet.RSD)e).get(e.get_parallel_dim()).containsSymbol(LoopTools.getLoopIndexSymbol(forloop)))
						e.Serialize();
				set.Expand(rd, Expand);
			}
			forloop=IRTools.getAncestorOfType(forloop, ForLoop.class);
		}
		for(Symbol ss: rd.getSymbols()){
			if(rd.getRange(ss) instanceof RangeExpression){
				for(SectionSet.SECTION e: set)
					if(e.containsSymbol(ss)){
						Set<Symbol> Expand = new HashSet<Symbol>();
						Expand.add(ss);
						if(e.isParallel() && !e.get_pfor().get_parallel_loop_index().equals(ss) && ((SectionSet.RSD)e).get(e.get_parallel_dim()).containsSymbol(ss))
							e.Serialize();
						set.Expand(rd, Expand);
					}
			}
		}
		return set;
	}
	
	private boolean isBarrierNode(DFANode node) {
        String tag = (String) node.getData("tag");
        if (tag != null && tag.equals("barrier")) {
            return true;
        }
        return false;
    }

}
