package ompd.analysis;

import java.util.*;

import cetus.hir.*;
import cetus.analysis.*;
import ompd.hir.OmpdAnnotation;

public class PCFGraph extends CFGraph {
    /**
     * Constructs a PCFGraph object with the given traversable object.
     * The entry node contains a string "ENTRY" for the key "stmt".
     *
     * @param t the traversable object.
     */
    public PCFGraph(Traversable t) {
        this(t, null);
    }

    /**
     * Constructs a PCFGraph object with the given traversable object and the
     * IR type whose sub graph is pruned. The resulting control
     * flow graph does contain the sub graphs for the specified IR type but those
     * sub graphs are not connected to/from the whole graph. Depending on the
     * applications of PCFGraph, those isolated sub graphs can be removed from or
     * reconnected to the whole graph.
     *
     * @param t         the traversable object.
     * @param supernode IR type that is pruned.
     */
    public PCFGraph(Traversable t, Class supernode) {
        super(t, supernode);
    }


//    protected DFAGraph buildDeclarationStatement(DeclarationStatement stmt) {
//        DFAGraph ret = new DFAGraph();
//        PrintTools.println("DeclarationStatement: " + stmt, 3);
//
//        DepthFirstIterator iter = new DepthFirstIterator(stmt);
//        while (iter.hasNext()) {
//            Object obj = iter.next();
//            if (obj instanceof Annotation) {
//                Annotation annot = (Annotation) obj;
//                // TODO: check this line is correct.
//                String annot_str = annot.toString();
//                System.out.println("before annot_str = " + annot_str);
//                annot_str = annot_str.replace("#pragma", "# pragma");
//                annot_str = annot_str.replace("/*", "/ *");
//                annot_str = annot_str.replace("//", "/ /");
//                if (annot_str.contains("# pragma")) {
//                    annot_str = annot_str.replace("(", " ( ");
//                    annot_str = annot_str.replace(")", " ) ");
//                    annot_str = annot_str.replace(":", " : ");
//                    annot_str = annot_str.replace(",", " , ");
//                }
//                System.out.println("after annot_str = " + annot_str);
//                String[] token_array = annot_str.split("\\s+");
//                if (token_array[0].compareTo("#") == 0 && token_array[1].compareTo("pragma") == 0) {
//                    if (token_array[2].equals("cetus")) {
//                        HashMap<String, Object> new_map = new HashMap<String, Object>();
//                        CetusAnnotationParser.parse_pragma(new_map, token_array);
//                        DFANode node = new DFANode();
//                        node.putData("DIPA", new_map);
//                        node.putData("ir", stmt);
//                        node.putData("stmt", stmt);
//                        ret.addNode(node);
//                    }
//                }
//            }
//        }
//        return ret;
//    }

    protected DFAGraph buildAnnotationStatement(AnnotationStatement stmt) {
        DFAGraph ret = new DFAGraph();

        OmpdAnnotation ompdAnnotation = stmt.getAnnotation(OmpdAnnotation.class, "barrier");

        if (ompdAnnotation != null) {
            DFANode node = new DFANode();
            node.putData("tag", "barrier");
            node.putData("type", ompdAnnotation.get("barrier"));
            node.putData("stmt", stmt);
            node.putData("source", ompdAnnotation.get("source"));
            ret.addNode(node);
        }

        return ret;
    }

/*
	protected DFAGraph buildAnnotationStatementRC(AnnotationStatementRC stmt)
	{
		DFAGraph ret = new DFAGraph();

		OmpAnnotationRC note = stmt.getAnnotation(OmpAnnotationRC.class, "barrier");
		if (note != null) 
		{
			DFANode node = new DFANode();	
			node.putDate("tag", "barrier");
			node.putDate("type", "barrier");

		List<AnnotationRC> annot_list = stmt.getAnnotations();
		for ( AnntationRC annot : annot_list )
		{
			if (annot instanceof OmpAnnotationRC)
			{
				OmpAnnotation omp_annot = (OmpAnnotation)annot;
				if (omp_annot.getText().compareTo("cetus")==0)
				{
				}
			}
		}

		return ret;
	}
*/

    // Build a graph for a for loop.
    protected DFAGraph buildForLoop(ForLoop stmt) {
        DFAGraph ret = new DFAGraph();

        CompoundStatement bs = (CompoundStatement) stmt.getBody();

        // Build nodes.
        DFANode init = new DFANode("stmt", stmt);
        DFANode condition = new DFANode("ir", stmt.getCondition());
        DFANode step = new DFANode("ir", stmt.getStep());
        DFANode exit = new DFANode("stmt-exit", stmt);

        // Delay links.
        break_link.push(new ArrayList());
        continue_link.push(new ArrayList());

        // Build subgraph.
        DFAGraph body = buildGraph(bs);

        // Put data.
        init.putData("ir", stmt.getInitialStatement());
        init.putData("for-condition", condition);
        init.putData("for-step", step);
        init.putData("for-exit", exit);

        // Keep special string for null condition (should be a unique entity).
        if (stmt.getCondition() == null) {
            condition.putData("ir", new NullStatement());
            //condition.putData("tag", "CONDITION"+System.identityHashCode(stmt));
        }
        condition.putData("true", body.getFirst());
        condition.putData("false", exit);
        condition.putData("back-edge-from", step);

        // Add loop variants
        condition.putData("loop-variants", DataFlowTools.getDefSymbol(stmt));
        if (!bs.getDeclarations().isEmpty()) {
            List symbol_exits = new ArrayList();
            symbol_exits.add(bs);
            exit.putData("symbol-exit", symbol_exits);
        }

        // Keep special string for null step (should be a unique entity).
        if (stmt.getStep() == null) {
            step.putData("ir", new NullStatement());
            //step.putData("tag", "STEP"+System.identityHashCode(stmt));
        }
        exit.putData("tag", "FOREXIT");

        // Add edges; init = ret[0] and exit = ret[last].
        ret.addEdge(init, condition);
        ret.addEdge(condition, body.getFirst());
        ret.absorb(body);
        if (!isJump(body.getLast()))
            ret.addEdge(body.getLast(), step);

        ret.addEdge(step, condition);
        ret.addEdge(step, exit);

        // Finalize delayed jumps.
        for (Object from : break_link.pop())
            ret.addEdge((DFANode) from, exit);
        for (Object from : continue_link.pop())
            ret.addEdge((DFANode) from, step);

        return ret;
    }

    private boolean isEmptyWithSingleSuccNode(DFANode node) {
        if (node.getSuccs().size() == 1 &&
            node.getData(Arrays.asList("stmt", "ir", "symbol-exit", "stmt-exit", "super-entry")) == null)
            return true;
        else
            return false;
    }

    /**
     * removable_node overrides the super class's removable_node in order not to
     * remove nodes with barrier tags.
     */
    protected boolean removable_node(DFANode node) {
        if (isEmptyWithSingleSuccNode(node)) {
            String tag = (String) node.getData("tag");
            if (tag != null && tag.compareTo("barrier") == 0) {
                DFANode next_node = null;
                for (DFANode nn : node.getSuccs()) {
                    next_node = nn;
                }
                // if the successor node is also a barrier, then remove the current one.
                // check this condition until the node is not empty or the node has more than
                // one successor
                while (isEmptyWithSingleSuccNode(next_node)) {
                    String next_tag = (String) next_node.getData("tag");
                    if (next_tag != null && next_tag.compareTo("barrier") == 0)
                        return true;
                    for (DFANode nn : next_node.getSuccs()) {
                        next_node = nn;
                    }
                }
                return false;
            } else
                return true;
        }

        return false;
    }

}
