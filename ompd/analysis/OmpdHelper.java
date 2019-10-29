package ompd.analysis;

import cetus.analysis.RangeAnalysis;
import cetus.analysis.Section;
import cetus.hir.*;
import ompd.hir.OMPDSTR;
import ompd.hir.OMPDTools;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import static cetus.hir.PrintTools.println;

public class OmpdHelper
{
    private static OmpdHelper ourInstance = null;
    private Program program = null;
    // the symbol for pid
    private Symbol pid_symbol = null;
    private Symbol i_symbol = null;
    private Symbol nprocs_symbol = null;

    private Procedure mainProc = null;
    private Map rangeMap = null;
    private PCFGraph cfg = null;

    public PCFGraph getCfg()
    {
        return cfg;
    }

    public void setCfg(PCFGraph cfg)
    {
        this.cfg = cfg;
    }

    public static OmpdHelper getInstance()
    {
        if(ourInstance == null)
            throw new InstantiationError("OmpdHelper is not initialized");

        return ourInstance;
    }

    public static Symbol getPIDSymbol()
    {
        return ourInstance.pid_symbol;
    }

    public static Symbol getiSymbol()
    {
        return ourInstance.i_symbol;
    }

    public static Symbol getNProcsSymbol()
    {
        return ourInstance.nprocs_symbol;
    }

    public static Procedure getMainProcedure()
    {
        return ourInstance.mainProc;
    }

    public static Map getRangeMap()
    {
        return ourInstance.rangeMap;
    }

    public static void initialize(Program program)
    {
        double timer;

        ourInstance = new OmpdHelper();

        ourInstance.program = program;
        // find the frequently used symbol from the global variables.
        for (Traversable t : program.getChildren())
        {
            TranslationUnit tu = (TranslationUnit) t;

            for (Symbol symbol : SymbolTools.getGlobalSymbols(tu))
            {
                if (symbol.getSymbolName().equals(OMPDSTR.PROCID))
                    ourInstance.pid_symbol = symbol;
                else if (symbol.getSymbolName().equals(OMPDSTR.NPROCS))
                    ourInstance.nprocs_symbol = symbol;
                else if (symbol.getSymbolName().equals(OMPDSTR.I))
                    ourInstance.i_symbol = symbol;
            }
        }
        if (ourInstance.pid_symbol == null)
        {
            Tools.exit(OMPDSTR.PROCID + " is not found in global scope.\n");
        }
        if (ourInstance.nprocs_symbol == null)
        {
            Tools.exit(OMPDSTR.NPROCS + " is not found in global scope.\n");
        }
        if (ourInstance.i_symbol == null)
        {
            Tools.exit(OMPDSTR.I + " is not found in global scope.\n");
        }

        ourInstance.mainProc = OMPDTools.findMain(program);
        assert ourInstance.mainProc != null;

        /* get the range map */
        timer = Tools.getTime();
        println("RangeAnalysis.getRanges() begins", 0);
        ourInstance.rangeMap = RangeAnalysis.getRanges(ourInstance.mainProc);
        println("RangeAnalysis.getRanges() ends in " + String.format("%.2f seconds", Tools.getTime(timer)), 0);
    }

    public Section.MAP replaceProcIdWithIndex(Section.MAP map)
    {
        BinaryOperator binary_op;
        IntegerLiteral offset_expr;
        for (Symbol symbol : map.keySet())
        {
            if (SymbolTools.isArray(symbol))
            {
                for (Section.ELEMENT element : map.get(symbol))
                {
                    for (Expression expr : element)
                    {
                        IRTools.replaceSymbolIn(expr, pid_symbol, new Identifier(i_symbol));
                    }
                }
            }
        }
        return map;
    }

    private OmpdHelper()
    {
    }
}
