package ompd.exec;

import static cetus.hir.PrintTools.println;

import java.io.*;
import java.util.*;

import cetus.analysis.*;
import cetus.hir.*;
import cetus.transforms.*;
import cetus.codegen.*;
import cetus.exec.*;
import ompd.codegen.*;


public class OMPDDriver extends Driver {

    protected OMPDDriver() {
        super();

        options.add("no-side-effect",
                "Assume there is no side-effect in the function calls");
        options.add("repetitive", "The input program is fully repeitive");
        options.add("turn-off-ersd", "The user deactivated delayed Symbolic Evaluation");
        options.add("turn-off-subtraction", "The user deactivated subtraction operations from global USE analysis");
        options.add("use-explicit-partitioning", "The compiler acts if explicit partitioning method is used by remove all advantages of using pi-notation");
        options.add("no-global-use", "do not perform Global USE analysis");
        options.add("no-communication", "do not perform communication generation analysis");
        options.add("print-bounds", "print out values of lower and upper bounds of each parallel loop");
        options.add("non-repetitive", "force the compiler to treat this program as non-repeititve");
    }

    /**
     * Runs this driver with args as the command line.
     *
     * @param args The command line from main.
     */
    public void run(String[] args) {
        parseCommandLine(args);

        /* collect files into "program" */
        parseFiles();

        /* OpenMP-D assumes input programs don't have aliased pointers */
        setOptionValue("alias", "0");
        setOptionValue("no-side-effect", "1");

        CodeGenPass.run(new ompd(program));
        

        PrintTools.printlnStatus("Printing...", 1);

        try {
            program.print();
        } catch (IOException e) {
            System.err.println("could not write output files: " + e);
            System.exit(1);
        }
    }

    /**
     * Entry point for Cetus; creates a new Driver object,
     * and calls run on it with args.
     *
     * @param args Command line options.
     */
    public static void main(String[] args) {
    	double timer = Tools.getTime();
        //println("OpenMP-D translation begins", 0);
        Driver driver = new OMPDDriver();
        driver.run(args);
        println("[ompd] translation ends in "
                + String.format("%.2f seconds", Tools.getTime(timer)), 0);
    }
}

