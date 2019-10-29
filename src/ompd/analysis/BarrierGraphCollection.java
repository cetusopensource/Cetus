package ompd.analysis;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import cetus.analysis.CFGraph;
import cetus.exec.Driver;
import cetus.hir.*;

public class BarrierGraphCollection
{
    private ArrayList<Symbol> id_maps;
    private ArrayList<BarrierGraph> graphs;
    private Procedure procedure;
    private PrevDefsFinder finder;

    private int verbosity = 5;

    public BarrierGraphCollection(Procedure p, Set<Symbol> set_symbol)
    {
        if (Driver.getOptionValue("verbosity") != null)
            verbosity = Integer.valueOf(Driver.getOptionValue("verbosity")).intValue();

        procedure = p;
        id_maps = new ArrayList<Symbol>(set_symbol);
        graphs = new ArrayList<BarrierGraph>();

        for (Symbol symbol : id_maps)
        {
            graphs.add(buildBarrierGraph(symbol));
        }
    }

    public int getID(Symbol symbol)
    {
        return id_maps.indexOf(symbol);
    }

    public BarrierGraph getSCFG(int index)
    {
        return graphs.get(index);
    }

    public BarrierGraph getSCFG(Symbol symbol)
    {
        return graphs.get(getID(symbol));
    }

    private BarrierGraph buildBarrierGraph(Symbol symbol)
    {
        // get a deep copy of the CFG.
        BarrierGraph result = new BarrierGraph(procedure, symbol, getID(symbol));

        if (verbosity >= 5)
        {
            PrintTools.println("Copied PCFGraph: symbol = " + result.getSymbolName() + "\n" + result, 5);
        }
        return result;
    }

    void serialize()
    {
    }

    public void genNodeUpdateFunctionCalls()
    {
        finder = new PrevDefsFinder(procedure, null);

        for (BarrierGraph graph : graphs)
        {
            graph.genNodeUpdateFunctionCalls(finder);
        }
    }

    public void genCodeForCFG()
    {

        List<Specifier> retType = new LinkedList<Specifier>();
        retType.add(Specifier.VOID);
        ProcedureDeclarator pDeclarator = new ProcedureDeclarator(new NameID("create_cfgs"), new LinkedList());
        CompoundStatement cStatement = new CompoundStatement();
        Procedure newProcedure = new Procedure(retType, pDeclarator, cStatement);
        ((TranslationUnit) procedure.getParent()).addDeclarationBefore(procedure, newProcedure);

        FunctionCall fc = new FunctionCall(new NameID("allocate_cfgs"));
        fc.addArgument(new IntegerLiteral(graphs.size()));
        ExpressionStatement eStatement = new ExpressionStatement(fc);
        newProcedure.getBody().addStatement(eStatement);

        for (BarrierGraph graph : graphs)
        {
            graph.genCodeForCFG(newProcedure);
        }
    }
}
