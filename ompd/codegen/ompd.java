package ompd.codegen;

import static cetus.hir.PrintTools.println;

import cetus.exec.Driver;
import ompd.analysis.*;
import ompd.transforms.*;

import cetus.codegen.*;
import cetus.hir.*;

public class ompd extends CodeGenPass {

    private int debug_level;

    public ompd(Program program) {
        super(program);
        debug_level = PrintTools.getVerbosity();
    }

    public String getPassName() {
        return "[ompd]";
    }

    public void start() {
    	double timer;
    	 timer = Tools.getTime();
    	 println("Parsing OpenMP directives begins", 0);
        /* Analyze OpenMP and generate ompd pragma */
        OmpAnalysisForOMPD omp = new OmpAnalysisForOMPD(program);
        omp.start();
        //PrintTools.println("OmpdAnalysisForOMPD is done.\n", 0);

        /* mark the synchronization points with AnnotationStatement */
        omp.mark_intervals();
        //PrintTools.println("OmpdAnalysisForOMPD.mark_intervals is done.\n", 0);
        println("Parsing OpenMP directives ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
    	
    	if(Driver.getOptionValue("use-explicit-partitioning")!=null)
    		println("The user has activated explicit static partitioning method", 0);
    	
    	if(Driver.getOptionValue("no-global-use")!=null)
    		println("Global USE analysis is disabled", 0);
    	
    	if(Driver.getOptionValue("no-communication")!=null)
    		println("Communication Generation is disabled", 0);
 
    	if(Driver.getOptionValue("repetitive")!=null)
    		println("User has activated repetitive flag", 0);   	
    	
    	if(Driver.getOptionValue("turn-off-ersd")!=null)
    		println("User has deactivated delayed Symbolic Evaluation (i.e.,No ERSDs)", 0);
    	
    	if(Driver.getOptionValue("turn-off-subtraction")!=null){
    		println("User has deactivated subtraction", 0);
    	}
        
        timer = Tools.getTime();
        println("SPMDizer begins", 0);
    	ProgramRecord prog_record = new ProgramRecord(program);	
        
    	/* Parallelize the loop with OpenMP Work sharing construct */
    	SPMDizer spmd = new SPMDizer(prog_record);
    	spmd.start();
    	println("SPMDizer ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
    	 if(prog_record.IsRepetitiveProgram())
     		println("Compiler determined that input program is repetitive", 0);
     	else
     		println("input program is non-repetitive", 0);
    	
    	/* Perform Reaching Analysis to compute MUST and MAY DEFlocal sections */
    	timer = Tools.getTime();
        println("Reaching Analysis begins", 0);
        OMPDReachAnalysis reach_analysis = new OMPDReachAnalysis(prog_record);
        reach_analysis.start();
        println("Reaching Analysis ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
        
        /* Perform Live Analysis to compute MAY USEglobal sections */
    	timer = Tools.getTime();
        println("Live Analysis begins", 0);
        OMPDLiveAnalysis live_analysis = new OMPDLiveAnalysis(prog_record);
        live_analysis.start();
        println("Live Analysis ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
        
    	timer = Tools.getTime();
        println("Code Generation pass begins", 0);
        GenerateCode generate_code = new GenerateCode(prog_record);
        generate_code.start();
        println("Code Generation pass ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
    }
}
