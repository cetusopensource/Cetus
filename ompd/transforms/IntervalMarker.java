package ompd.transforms;

import cetus.hir.*;
import cetus.transforms.TransformPass;
import ompd.hir.OMPDTools;
import ompd.hir.OmpdAnnotation;

import java.util.Iterator;
import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: putt
 * Date: 5/23/13
 * Time: 3:44 PM
 */
public class IntervalMarker extends TransformPass
{
    private Program program;

    public IntervalMarker(Program prog)
    {
        super(prog);
        program = prog;
    }

    @Override
    public String getPassName()
    {
        return "[Interval Marker]";
    }

    /**
     * Implicit barrier
     * - at the beginning of the parallel for construct
     * - at the end of the parallel construct
     * - at the end of the worksharing construct (check an existence of nowait clause)
     * - at the end of the sections construct (check an existence of nowait clause)
     * - at the end of the single construct (check an existence of nowait clause)
     */

    @Override
    public void start()
    {
        List<OmpdAnnotation> ompdAnnotationList = OMPDTools.collectPragmas(program, OmpdAnnotation.class);

        for (OmpdAnnotation ompdAnnotation : ompdAnnotationList)
        {
            Object obj = ompdAnnotation.getAnnotatable();
            if (!(obj instanceof Statement))
                continue;

            Statement ownerStatement;
            CompoundStatement parentStatement;

            ownerStatement = (Statement) obj;
            parentStatement = (CompoundStatement) ownerStatement.getParent();
            if (ompdAnnotation.containsKey("parallel") && ompdAnnotation.containsKey("for"))
            {
                /*
                * No need to make a barrier before a parallel region, because
                *   1. DEF's in serial region are already shared by all processes.
                *   2. If there is a parallel region before this parallel region,
                *      the previous parallel region already created a barrier.
                * parent_stmt.addStatementBefore(attached_stmt, insertBarrier(attached_stmt, "S2P"));
                */
                // 2011-02-24 okwan's test
                // def analysis failed passing DEF information collected in a work sharing loop with nowait clause
                // to the next barrier. Thus, temporarily, it is okay not to handle nowait clauses.
                //                if (ompdAnnotation.containsKey("nowait") == false)
                {
                    Statement prevStmt = getPreviousStatement(ownerStatement);
                    boolean addBarrierBefore = true;
                    String prevBarrierType = "";
                    OmpdAnnotation prevAnnot = null;

                    if(prevStmt instanceof AnnotationStatement)
                    {
                        AnnotationStatement annotStmt = (AnnotationStatement) prevStmt;
                        OmpdAnnotation annot = annotStmt.getAnnotation(OmpdAnnotation.class, "barrier");

                        if(annot != null && annot.containsKey("barrier"))
                        {
                            addBarrierBefore = false;
                            prevBarrierType = annot.get("barrier");
                            prevAnnot = annot;
                        }
                    }

                    if(addBarrierBefore)
                    {
                        parentStatement.addStatementBefore(ownerStatement, insertBarrier(ownerStatement, "S2P"));
                    }
                    else
                    {
                        if(prevBarrierType.compareTo("P2S") == 0)
                        {
                            prevAnnot.put("barrier", "P2P");
                        }
                    }
                    parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2S"));
                }
            }
            else if (ompdAnnotation.containsKey("parallel"))
            {
                parentStatement.addStatementBefore(ownerStatement, insertBarrier(ownerStatement, "S2P"));
                parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2S"));

                PrintTools.println("[mark] parent_stmt", 10);
                PrintTools.println(parentStatement.toString(), 10);
            }
            else if (ompdAnnotation.containsKey("for") || ompdAnnotation.containsKey("sections") ||
                    ompdAnnotation.containsKey("single"))
            {
                // 2011-02-24 okwan's test, same reason as above.
                //                if (ompdAnnotation.containsKey("nowait") == false)
                {
                    parentStatement.addStatementAfter(ownerStatement, insertBarrier(ownerStatement, "P2P"));
                }
            }
            else if (ompdAnnotation.containsKey("barrier"))
            {
                /* store source statement that will be used in PCFG */
                ompdAnnotation.put("source", ownerStatement);
            }
        }
    }

    private AnnotationStatement insertBarrier(Statement stmt, String type)
    {
        OmpdAnnotation ompdAnnotation = new OmpdAnnotation();
        ompdAnnotation.put("barrier", type);
        ompdAnnotation.put("source", stmt);
        AnnotationStatement annot_stmt = new AnnotationStatement(ompdAnnotation);
        return annot_stmt;
    }

    private Statement getPreviousStatement(Statement stmt)
    {
        CompoundStatement parentStatement = (CompoundStatement) stmt.getParent();
        List children = parentStatement.getChildren();

        Statement prevStmt = null;
        Statement curStmt = null;
        Iterator iter = children.iterator();

        if(iter.hasNext())
            prevStmt = (Statement) iter.next();

        if(prevStmt == stmt)
            return null;

        while (iter.hasNext())
        {
            curStmt = (Statement) iter.next();

            if (curStmt == stmt)
                return prevStmt;
            else
                prevStmt = curStmt;
        }
        return null;
    }
}
