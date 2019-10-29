package ompd.hir;

import java.util.*;

import cetus.analysis.LoopTools;
import cetus.analysis.RangeDomain;
import cetus.analysis.Relation;
import cetus.hir.*;

public class OMPDParallelForLoop {
	
	private ForLoop forloop;
	private Expression orig_lb, orig_ub, step;
	private int loopId;
	private Symbol parallel_loop_index;
	private RangeDomain RangeInfo;
	
	private boolean repetitive;; 
	private Loop OuterSerialLoop; // innermost outer serial loop
	//private ArrayList<Loop> OuterSerialLoops; // ordered from outermost to innermost 
	
	
	public OMPDParallelForLoop (ForLoop loop){
		//super(loop.getInitialStatement(), loop.getCondition(), loop.getStep(), loop.getBody());
		this.forloop = loop;
		this.orig_lb = LoopTools.getLowerBoundExpression(loop).clone();
        this.orig_ub = LoopTools.getUpperBoundExpression(loop).clone();
		this.step = LoopTools.getIncrementExpression(loop).clone();
		this.parallel_loop_index = LoopTools.getLoopIndexSymbol(loop);
		//this.num_of_iterations = Symbolic.simplify(Symbolic.divide(Symbolic.add(Symbolic.subtract(orig_ub.clone(), orig_lb.clone()),step.clone()),step.clone()));	
		this.repetitive=false; // default value  
		this.OuterSerialLoop = null;
		//this.OuterSerialLoops = new ArrayList<Loop>();
	}
	
	public ForLoop get_Forloop() {
		return this.forloop;
	}
	
	public Expression get_orig_lb() {
		return this.orig_lb;
	}
	
	public Expression get_orig_ub() {
		return this.orig_ub;
	}
	
	public Expression get_step() {
		return this.step;
	}
	
	public void set_RangeInfo(RangeDomain rd){
		this.RangeInfo = rd;
		orig_lb = RangeInfo.substituteForward(orig_lb);
        orig_ub = RangeInfo.substituteForward(orig_ub);
        step = RangeInfo.substituteForward(step);
	}
	public RangeDomain get_RangeInfo() {
		return this.RangeInfo;
	}
	
	public Symbol get_parallel_loop_index(){
		return this.parallel_loop_index;
	}
	
	public void MakeNonRepetitive(){
		this.repetitive=false;
	}
	
	public void MakeRepetitive(){
		this.repetitive=true;
	}
	
	public boolean IsRepetitive(){
		return this.repetitive;
	}
	
	public Loop get_outer_serial_loop(){
		return this.OuterSerialLoop;
	}
	
	public void set_outer_serial_loop(Loop outer ){
		 this.OuterSerialLoop = outer;
	}
	
	/*public void add_outer_serial_loop(Loop serial_loop){
		this.OuterSerialLoops.add(serial_loop);
	}
	
	public ArrayList<Loop> get_OuterSerialLoops(){
		return this.OuterSerialLoops;
	}*/
	
	public void set_loopId(int Id){
		this.loopId=Id;
	}
	public int get_loopId(){
		return this.loopId;
	}
	public String toString(){
		return this.forloop.toString();
	}
    
    public static boolean IsSimilar(OMPDParallelForLoop pfor1, OMPDParallelForLoop pfor2, RangeDomain rd){
    	if(pfor1==null || pfor2==null)
    		return false;
    	RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;
    	Relation lb_rel = rd2.compare(pfor1.get_orig_lb(), pfor2.get_orig_lb());
		Relation ub_rel = rd2.compare(pfor1.get_orig_ub(), pfor2.get_orig_ub());
		Relation stride_rel = rd2.compare(pfor1.get_step(), pfor2.get_step());
		if(lb_rel.isEQ() && ub_rel.isEQ() && stride_rel.isEQ())
			return true;
		return false;
    }


}
