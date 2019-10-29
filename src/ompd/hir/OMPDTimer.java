package ompd.hir;

import cetus.hir.*;

public enum OMPDTimer {
    STARTUP("OMPD_TIMER_STARTUP"),
    CFG_INIT("OMPD_TIMER_CFG_INIT"),
    BOUND_INIT("OMPD_TIMER_BOUND_INIT"),
    SECTION_UPDATE("OMPD_TIMER_SECTION_UPDATE"),
    CFG_EVAL("OMPD_TIMER_CFG_EVAL"),
    INTERSECTION("OMPD_TIMER_INTERSECTION"),
    MPI_COMM("OMPD_TIMER_MPI_COMM"),
    ALLREDUCE("OMPD_TIMER_ALLREDUCE"),
    ALLGATHER("OMPD_TIMER_ALLGATHER");

    private String name;

    OMPDTimer(String string) {
        name = string;
    }

    public String toString() {
        return name;
    }

    public static void insertTimerStartBefore(Statement here, OMPDTimer type) {
        CompoundStatement parent = IRTools.getAncestorOfType(here, CompoundStatement.class);
        String string = "OMPD_TIMER_START(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        AnnotationStatement annotationStatement = new AnnotationStatement(codeAnnotation);
        parent.addStatementBefore(here, annotationStatement);
    }

    public static void insertTimerStopBefore(Statement here, OMPDTimer type) {
        CompoundStatement parent = IRTools.getAncestorOfType(here, CompoundStatement.class);
        String string = "OMPD_TIMER_STOP(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        AnnotationStatement annotationStatement = new AnnotationStatement(codeAnnotation);
        parent.addStatementBefore(here, annotationStatement);
    }

    public static void insertTimerStartAfter(Statement here, OMPDTimer type) {
        CompoundStatement parent = IRTools.getAncestorOfType(here, CompoundStatement.class);
        String string = "OMPD_TIMER_START(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        AnnotationStatement annotationStatement = new AnnotationStatement(codeAnnotation);
        parent.addStatementAfter(here, annotationStatement);
    }

    public static void insertTimerStopAfter(Statement here, OMPDTimer type) {
        CompoundStatement parent = IRTools.getAncestorOfType(here, CompoundStatement.class);
        String string = "OMPD_TIMER_STOP(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        AnnotationStatement annotationStatement = new AnnotationStatement(codeAnnotation);
        parent.addStatementAfter(here, annotationStatement);
    }

    public static Annotation getTimerStartAnnotation(OMPDTimer type) {
        String string = "OMPD_TIMER_START(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        return codeAnnotation;
    }

    public static Annotation getTimerStopAnnotation(OMPDTimer type) {
        String string = "OMPD_TIMER_STOP(" + type + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        return codeAnnotation;
    }

    public static void encloseByTimerCode(Statement statement, OMPDTimer type) {
        /* annotate timing code before and after the for loop */
        Annotation before = OMPDTimer.getTimerStartAnnotation(type);
        statement.annotateBefore(before);
        Annotation after = OMPDTimer.getTimerStopAnnotation(type);
        statement.annotateAfter(after);
    }

    public static void encloseByTimerStatement(Statement statement, OMPDTimer type) {
        insertTimerStartBefore(statement, type);
        insertTimerStopAfter(statement, type);
    }

    public static Annotation getCommTimerStartAnnotation(int barrierId) {
        String string = "OMPD_COMM_TIMER_START(" + barrierId + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        return codeAnnotation;
    }

    public static Annotation getCommTimerStopAnnotation(int barrierId) {
        String string = "OMPD_COMM_TIMER_STOP(" + barrierId + ");";
        CodeAnnotation codeAnnotation = new CodeAnnotation(string);
        return codeAnnotation;
    }
    public static void encloseByCommTimerCode(Statement statement, int barrierId) {
        /* annotate timing code before and after the for loop */
        Annotation before = OMPDTimer.getCommTimerStartAnnotation(barrierId);
        statement.annotateBefore(before);
        Annotation after = OMPDTimer.getCommTimerStopAnnotation(barrierId);
        statement.annotateAfter(after);
    }
}
