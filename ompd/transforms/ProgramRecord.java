package ompd.transforms; 

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Set;
import java.util.Map;

import ompd.analysis.PCFGraph;
import ompd.hir.OMPDParallelForLoop;
import ompd.hir.OMPDTools;
import ompd.hir.OmpdAnnotation;
import cetus.analysis.RangeAnalysis;
import cetus.exec.Driver;
import cetus.hir.*;

class LoopRecordItem extends IdentityHashMap<OmpdAnnotation, OMPDParallelForLoop>{
	
	LoopRecordItem(){
		super();
	}
	
	public void add(OmpdAnnotation key, OMPDParallelForLoop value ){
		put(key, value); 
	}
	
	public OMPDParallelForLoop get_loop_record(OmpdAnnotation key){
		return get(key);
	}
	
	public Set<OmpdAnnotation> get_keys(){
		return keySet();
	}
	
}

 
class ProcedureRecordItem {
	 private LoopRecordItem loop_record;
	 private Map range_map; // I never needed this 
	 private int barriers_count; // I never needed this 
	 private PCFGraph cfg;
	 ArrayList<Loop> OuterSerialLoops; // I never needed this 
	 private BoundRecord bound_record;
	 
	 public ProcedureRecordItem(){
		 loop_record = new LoopRecordItem();
		 bound_record = new BoundRecord();
	 }
	 
	 public void add_loop_to_proc_in_tu(OmpdAnnotation annot, OMPDParallelForLoop pfor ){
		 loop_record.add(annot, pfor);
		}
	 
	 public OMPDParallelForLoop get_loop_record(OmpdAnnotation annot){
			return loop_record.get_loop_record(annot);
		}
	 
	 public Set<OmpdAnnotation> get_loop_annot_keys(){
			return loop_record.get_keys();
		}
	 
	 public void set_ramp(Map rmap){
		 this.range_map = rmap;
	 }
	 
	 public Map get_ramp(){
		 return this.range_map;
	 }
	 
	 public void set_barriers_count(int cnt){
		 this.barriers_count = cnt;
	 }
	 
	 public int get_barriers_count(){
		 return this.barriers_count;
	 }
	 
	 public void set_PCFGraph(PCFGraph cg){
		 this.cfg = cg;
	 }
	 
	 public PCFGraph get_PCFGraph(){
		 return this.cfg;
	 }
	 
	 public void set_bound_record(BoundRecord rcd){
		 this.bound_record = rcd;
	 }
	 
	 public BoundRecord get_bound_record(){
		 return this.bound_record;
	 }
	 
	 public void set_OuterSerialLoopsSet(ArrayList<Loop> st){
		 this.OuterSerialLoops = st;
	 }
	 
	 public ArrayList<Loop> get_OuterSerialLoopsSet(){
		 return this.OuterSerialLoops;
	 }
 }
 
 class TURecordItem extends IdentityHashMap<Procedure,ProcedureRecordItem> {
	 
	 public TURecordItem(){
		 super();
	 }
	 
	 public void add(Procedure key, ProcedureRecordItem value){
		 put(key, value);
	 }
	 
	 public Set<Procedure> get_proc_keys(){
		 return keySet();
	 }
	 
	 public void add_loop_to_proc_in_tu(Procedure proc, OmpdAnnotation annot, OMPDParallelForLoop pfor ){
			get(proc).add_loop_to_proc_in_tu(annot, pfor);
		}
	 
	 public OMPDParallelForLoop get_loop_record(Procedure proc, OmpdAnnotation annot){
			return get(proc).get_loop_record(annot);
		}
	 
	 public Set<OmpdAnnotation> get_loop_annot_keys(Procedure proc){
			return get(proc).get_loop_annot_keys();
		}
	 
	 public void set_ramp(Procedure proc, Map rmap){
		 get(proc).set_ramp(rmap);
	 } 
	 
	 public Map get_range_map(Procedure proc){
			return get(proc).get_ramp();
	 }
	 
	 public void set_bound_record(Procedure proc, BoundRecord rcd){
		 get(proc).set_bound_record(rcd);
	 }
	 
	 public BoundRecord get_bound_record(Procedure proc){
		 return get(proc).get_bound_record();
	 }
	 
	 public void set_barriers_count(Procedure proc, int cnt){
		 get(proc).set_barriers_count(cnt);
	 }
	 
	 public int get_barriers_count(Procedure proc){
		 return get(proc).get_barriers_count();
	 }
	 
	 public void set_PCFGraph(Procedure proc, PCFGraph cg){
		 get(proc).set_PCFGraph(cg);
	 }
	 
	 public PCFGraph get_PCFGraph(Procedure proc){
		 return get(proc).get_PCFGraph();
	 }
	 
	 public void set_OuterSerialLoopsSet(Procedure proc, ArrayList<Loop> st){
		 get(proc).set_OuterSerialLoopsSet(st);
	 }
	 
	 public ArrayList<Loop> get_OuterSerialLoopsSet(Procedure proc){
		 return get(proc).get_OuterSerialLoopsSet();
	 }
	 
 }
 
 class TURecord extends IdentityHashMap<TranslationUnit,TURecordItem> {
	 public TURecord(){
		 super();
	 }
	 
	 public void add(TranslationUnit key, TURecordItem value){
		 put(key, value);
	 }
	 
	 public void add_proc_to_tu_record(TranslationUnit tu, Procedure proc){
		 get(tu).put(proc, new ProcedureRecordItem());
	 }
	 
	 public Set<Procedure> get_procs(TranslationUnit tu){
		 return get(tu).get_proc_keys();
	 }
	 
 }

public class ProgramRecord {
	private Program prog;
	private TURecord tu_record;
	private Procedure mainProc = null;
	private TranslationUnit globals;
	private Symbol procid_symbol, nprocs_symbol, loop_i_symbol;
	private boolean IsRepetitive;
	
	public ProgramRecord(Program program){
		prog = program;
		tu_record = new TURecord();
		mainProc = OMPDTools.findMain(program);
		assert mainProc != null;
		globals = new TranslationUnit("ompd_globals.h");
		IsRepetitive = false; // by default, programs are non repetitive
		if(Driver.getOptionValue("repetitive")!=null) // if user says the program is repetitive, so be it
			IsRepetitive = true; 
		
		for (Traversable t : program.getChildren()) {
            if (!(t instanceof TranslationUnit)) {
                continue;
            }
            TranslationUnit tu = (TranslationUnit) t;
            tu_record.add(tu, new TURecordItem());

            PrintTools.println("Input file name = " + tu.getInputFilename(), 5);

            DepthFirstIterator proc_iter = new DepthFirstIterator(tu);
            proc_iter.pruneOn(Procedure.class);
            Set<Procedure> proc_set = proc_iter.getSet(Procedure.class);
            for (Procedure proc : proc_set) {
            	tu_record.add_proc_to_tu_record(tu, proc);
            }
		}
		declareOmpdVariables();
	}
	
	public void MakeRepetitiveProgram(){ // this is set by the SPMDizer step if it proves that the program is repetitive
		this.IsRepetitive = true;
	}
	
	public boolean IsRepetitiveProgram(){
		return this.IsRepetitive;
	}
	
	public Set<TranslationUnit> get_TUs(){
		return tu_record.keySet();
	}
	
	public Set<Procedure> get_Procedures_of_TU(TranslationUnit tu){
		return tu_record.get_procs(tu);
	}
	
	public void add_loop_to_proc_in_tu(TranslationUnit tu, Procedure proc, OmpdAnnotation annot, OMPDParallelForLoop pfor ){
		tu_record.get(tu).add_loop_to_proc_in_tu(proc,annot, pfor);
	}
	
	public OMPDParallelForLoop get_loop_record(TranslationUnit tu, Procedure proc, OmpdAnnotation annot){
		return tu_record.get(tu).get_loop_record(proc,annot);
	}
	
	public Set<OmpdAnnotation> get_loop_annot_keys(TranslationUnit tu, Procedure proc){
		return tu_record.get(tu).get_loop_annot_keys(proc);
	}
	
	public Procedure get_main(){
		return this.mainProc;
	}
	
	public Program get_program(){
		return this.prog;
	}
	
/*I never needed this function ... RangeAnalysis Info is computed somewhere else */
//this function computes ranges of each procedure in each TU, intra-procedurally 
	public void compute_ranges(){
		for(TranslationUnit tu : get_TUs() )
			for(Procedure proc : get_Procedures_of_TU(tu)){
				Map rmap = RangeAnalysis.getRanges(proc);
				tu_record.get(tu).set_ramp(proc,rmap);
			}
	}
	
	public Map get_range_map(TranslationUnit tu, Procedure proc){
		return tu_record.get(tu).get_range_map(proc);
	}
	
	public void set_barriers_count(TranslationUnit tu, Procedure proc, int cnt){
		tu_record.get(tu).set_barriers_count(proc, cnt);
	 }
	
	 public int get_barriers_count(TranslationUnit tu, Procedure proc){
		 return tu_record.get(tu).get_barriers_count(proc);
	 }
	 
	 public void set_bound_record(TranslationUnit tu, Procedure proc, BoundRecord rcd){
		 tu_record.get(tu).set_bound_record(proc,rcd);
	 }
	 
	 public BoundRecord get_bound_record(TranslationUnit tu, Procedure proc){
		 return tu_record.get(tu).get_bound_record(proc);
	 }
	 
	 public void set_PCFGraph(TranslationUnit tu, Procedure proc, PCFGraph cg){
		 tu_record.get(tu).set_PCFGraph(proc,cg);
	 }
	 
	 public PCFGraph get_PCFGraph(TranslationUnit tu, Procedure proc){
		 return tu_record.get(tu).get_PCFGraph(proc);
	 }
	 
	 public void set_OuterSerialLoopsSet(TranslationUnit tu, Procedure proc, ArrayList<Loop> st){
		 tu_record.get(tu).set_OuterSerialLoopsSet(proc,st);
	 }
	 
	 public ArrayList<Loop> get_OuterSerialLoopsSet(TranslationUnit tu, Procedure proc){
		 return tu_record.get(tu).get_OuterSerialLoopsSet(proc);
	 }
	 
	 private void declareOmpdVariables() {
	        NameID nprocs_id, procid_id, loop_i_id;

	        // TODO: using a string directly is a bad idea
	        nprocs_id = new NameID("ompd_nprocs");
	        procid_id = new NameID("ompd_procid");
	        loop_i_id = new NameID("ompd_i");

	        VariableDeclarator nprocs_declarator = new VariableDeclarator(nprocs_id);
	        nprocs_symbol = nprocs_declarator;
	        Declaration nprocs_decl = new VariableDeclaration(Specifier.INT, nprocs_declarator);
	        

	        VariableDeclarator procid_declarator = new VariableDeclarator(procid_id);
	        procid_symbol = procid_declarator;
	        Declaration procid_decl = new VariableDeclaration(Specifier.INT, procid_declarator);
	       

	        VariableDeclarator loop_i_declarator = new VariableDeclarator(loop_i_id);
	        loop_i_symbol = loop_i_declarator;
	        Declaration loop_i_decl = new VariableDeclaration(Specifier.INT, loop_i_declarator);
	        
	         //already added to ompd_interface.h 
	        //globals.addDeclarationFirst(nprocs_decl);
	        //globals.addDeclarationFirst(procid_decl);
	        //globals.addDeclarationFirst(loop_i_decl);
	 }
	 
	 public TranslationUnit get_globalsTU(){
		 return this.globals;
	 }	 
	 public Symbol get_procid(){
		 return this.procid_symbol;
	 }	 
	 public Symbol get_nprocs(){
		 return this.nprocs_symbol;
	 }	 
	 public Symbol get_loop_i(){
		 return this.loop_i_symbol;
	 }

}
