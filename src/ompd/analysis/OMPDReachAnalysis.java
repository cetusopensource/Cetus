package ompd.analysis;

import java.util.*;

import ompd.hir.OMPDParallelForLoop;
import ompd.hir.OMPDTools;
import ompd.transforms.ProgramRecord;
import ompd.hir.SectionSet;

import cetus.analysis.DFANode;
import cetus.analysis.RangeDomain;
import cetus.hir.*;

public class OMPDReachAnalysis {
	private PCFGraph cfg;
	private Set<Symbol> shared_vars, shared_arrays;
	private ProgramRecord prog_record;
	Map<DFANode,SectionSet.MAP> DEFSetsofStatements;
	
	public OMPDReachAnalysis(ProgramRecord rcd){
		this.prog_record = rcd;
	}
	
	public void start(){
		for (TranslationUnit tu : prog_record.get_TUs()) {
            for (Procedure proc : prog_record.get_Procedures_of_TU(tu)) {
            	cfg = prog_record.get_PCFGraph(tu, proc);
            	//range_map = prog_record.get_range_map(tu, proc);
            	shared_arrays = OMPDTools.getSharedArrays(proc);
            	shared_vars = OMPDTools.getSharedVariables(proc);
            	performReachAnalysis();
            }
		}
	}
	
	private void performReachAnalysis(){

		DEFSetsofStatements = new HashMap<DFANode,SectionSet.MAP>();
		computeDEFSetsofStatements();
		computeMustDEFSetsofSPMDBlocks();
		//computeMayDEFSetsofSPMDBlocks();
		DEFSetsofStatements=null;
		
	}

	/** computes write sets of each statement. Those sets represent GEN sets of Local DEF analysis*/
	private void computeDEFSetsofStatements(){
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
	            			        (OMPDParallelForLoop)node.getData("inside_pfor")); 
	            		//node.putData("DEF", new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(DEF)));
	            		DEFSetsofStatements.put(node, new SectionSet.MAP(SymbolTools.getSymbolOf(ac), new SectionSet(DEF)));
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
		
	}
	
	private void computeMustDEFSetsofSPMDBlocks(){
		int count=0;
		 TreeMap work_list = new TreeMap();
		 // Enter the entry node in the work_list
	     DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
	     Map<DFANode,SectionSet.MAP> sections_in = new HashMap<DFANode,SectionSet.MAP>();
	     Map<DFANode,SectionSet.MAP> sections_out = new HashMap<DFANode,SectionSet.MAP>();
	     //entry.putData("must_def_in", new SectionSet.MAP());
	     sections_in.put(entry, new SectionSet.MAP());
	     work_list.put(entry.getData("top-order"), entry);	
	     
	  // Do iterative steps to compute must_def_in & must_def_out
	     while (!work_list.isEmpty()) {
	    	 if (count++ > (cfg.size() * 10)) {
	                PrintTools.println(cfg.toDot("tag,ir,ueuse", 3), 0);
	                PrintTools.println("cfg size = " + cfg.size(), 0);
	                Tools.exit("[localAnalysis] infinite loop!");
	         }
	    	 DFANode node = (DFANode) work_list.remove(work_list.firstKey());
	         SectionSet.MAP must_def_in = null;
	         
	         for (DFANode pred : node.getPreds()) {
	        	 //SectionSet.MAP pred_must_def_out = (SectionSet.MAP) pred.getData("must_def_out");
	        	 SectionSet.MAP pred_must_def_out = sections_out.get(pred);
	        	 
	        	 if (must_def_in == null) {
	                    must_def_in =  pred_must_def_out.clone();
	                } else {
	                    DFANode temp = (DFANode) node.getData("back-edge-from");
	                    if (temp != null && temp == pred) {
	                        // this data is from a back-edge, union it with the current data
	                        must_def_in = must_def_in.unionWith(pred_must_def_out, (RangeDomain) node.getData("range_in"));
	                    } else {
	                        // this is an if-else branch, thus intersect it with the current data
	                        must_def_in = must_def_in.intersectWith(pred_must_def_out, (RangeDomain) node.getData("range_in"));
	                    }
	                }
	         }
	         
	         // previous must_def_in
	         //SectionSet.MAP p_must_def_in = (SectionSet.MAP) node.getData("must_def_in");
	         SectionSet.MAP p_must_def_in = sections_in.get(node);
             if(p_must_def_in==null || p_must_def_in.hasChanged(must_def_in, (RangeDomain) node.getData("range_in"))){
            	 //node.putData("must_def_in", must_def_in);
            	 sections_in.put(node, must_def_in);

                 
                 if(isBarrierNode(node)){
                	 //node.putData("must_def_out", new SectionSet.MAP() );
                	 sections_out.put(node, new SectionSet.MAP());
                 }
                 else{
                	 if(must_def_in == null){
                		 if(/*(node.getData("DEF"))*/DEFSetsofStatements.get(node)==null){
                			 //node.putData("must_def_out", new SectionSet.MAP() );
                			 sections_out.put(node, new SectionSet.MAP());
                		 }
                		 else{
                			 //SectionSet.MAP tmp = (SectionSet.MAP)((SectionSet.MAP)node.getData("DEF")).clone();
                			 SectionSet.MAP tmp = DEFSetsofStatements.get(node).clone();
                			 if(!tmp.isEmpty())
                				 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                			 //node.putData("must_def_out", tmp );
                			 sections_out.put(node, tmp);
                		 }
                     }
                	 else if(node.getData("inside_pfor") == null){
                		 SectionSet.MAP tmp = (SectionSet.MAP)must_def_in.clone();
                		 if(!tmp.isEmpty())
                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                		 //node.putData("must_def_out", tmp );
                		 sections_out.put(node, tmp);
                	 }
                	 else{
                		 //SectionSet.MAP tmp = must_def_in.unionWith((SectionSet.MAP)node.getData("DEF"), (RangeDomain) node.getData("range_out"));
                		 SectionSet.MAP tmp = must_def_in.unionWith(DEFSetsofStatements.get(node), (RangeDomain) node.getData("range_out"));
                		 if(!tmp.isEmpty())
                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                		 //node.putData("must_def_out", tmp );
                		 sections_out.put(node, tmp);
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
	     entry=null;
	     sections_out=null;
	     AttachToNodes("must_def_in", sections_in);
	     sections_in=null;
	     
	}
	
	private void computeMayDEFSetsofSPMDBlocks(){
		int count=0;
		TreeMap work_list = new TreeMap();
		 // Enter the entry node in the work_list
	     DFANode entry = cfg.getNodeWith("stmt", "ENTRY");
	     entry.putData("may_def_in", new SectionSet.MAP());
	     work_list.put(entry.getData("top-order"), entry);	
	     
		  // Do iterative steps to compute may_def_in & may_def_out
	     while (!work_list.isEmpty()) {
	    	 if (count++ > (cfg.size() * 10)) {
	                PrintTools.println(cfg.toDot("tag,ir,ueuse", 3), 0);
	                PrintTools.println("cfg size = " + cfg.size(), 0);
	                Tools.exit("[localAnalysis] infinite loop!");
	         }
	    	 DFANode node = (DFANode) work_list.remove(work_list.firstKey());
	         SectionSet.MAP may_def_in = null;
	         
	         for (DFANode pred : node.getPreds()) {
	        	 SectionSet.MAP pred_may_def_out = (SectionSet.MAP) pred.getData("may_def_out");
	        	 
	        	 if (may_def_in == null) {
	                    may_def_in = (SectionSet.MAP) pred_may_def_out.clone();
	             } else {
	                    may_def_in = may_def_in.unionWith(pred_may_def_out, (RangeDomain) node.getData("range_in"));
	             }
	         }
	         
	         // previous may_def_in
             SectionSet.MAP p_may_def_in = (SectionSet.MAP) node.getData("may_def_in");             
             if(p_may_def_in==null || p_may_def_in.hasChanged(may_def_in, (RangeDomain) node.getData("range_in"))){
            	 node.putData("may_def_in", may_def_in);

                 if(isBarrierNode(node)){
                	 node.putData("may_def_out", new SectionSet.MAP() );
                 }
                 else{
                	 if(may_def_in == null){
                		 if((node.getData("DEF"))==null)
                			 node.putData("may_def_out", new SectionSet.MAP() );
                		 else{
                			 SectionSet.MAP tmp = (SectionSet.MAP)((SectionSet.MAP)node.getData("DEF")).clone();
                			 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                			 node.putData("may_def_out", tmp );
                		 }
                     }
                	 else if(node.getData("inside_pfor") == null){
                		 SectionSet.MAP tmp = (SectionSet.MAP)may_def_in.clone();
                		 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                		 node.putData("may_def_out", tmp );
                	 }
                	 else{
                		 SectionSet.MAP tmp = may_def_in.unionWith((SectionSet.MAP)node.getData("DEF"), (RangeDomain) node.getData("range_out"));
                		 tmp.Expand((RangeDomain) node.getData("range_out"), (Set<Symbol>)node.getData("ExpandableSymbolSet"));
                		 node.putData("may_def_out", tmp );
                	 }
                 }
                 
                 for (DFANode succ : node.getSuccs()) {
                     work_list.put(succ.getData("top-order"), succ);
                 }
             }
	         
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
	
	private SectionSet.SECTION getSection(ArrayAccess expr,RangeDomain rd, Set<Symbol> Expand, OMPDParallelForLoop pfor){
	//	ArrayAccess ar = (ArrayAccess) rd.substituteForward(expr);
		SectionSet.RSD DEF= null;
		if(pfor != null)
			DEF = new SectionSet.RSD(expr,rd,Expand,pfor);
		else
			DEF = new SectionSet.RSD(expr,rd,Expand);
		DEF.set_FullSized((ArraySpecifier)SymbolTools.getSymbolOf(expr).getArraySpecifiers().get(0));
		return DEF; 
	}
	
	private boolean isBarrierNode(DFANode node) {
        String tag = (String) node.getData("tag");
        if (tag != null && tag.equals("barrier")) {
            return true;
        }
        return false;
    }
}
