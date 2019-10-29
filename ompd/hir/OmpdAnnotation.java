package ompd.hir;

import cetus.hir.Expression;
import cetus.hir.PragmaAnnotation;
import cetus.hir.PrintTools;
import cetus.hir.Symbol;

import java.util.*;

public class OmpdAnnotation extends PragmaAnnotation {
    private static final List<String> keywords = Arrays.asList(
        /* directives */
        "parallel", "for", "sections", "section", "single", "task", "master",
        "critical", "barrier", "taskwait", "atomic", "flush", "ordered",
        "threadprivate",

        /* clauses */
        "if", "num_threads", "default", "shared", "private", "firstprivate",
        "lastprivate", "reduction", "copyin", "copyprivate", "schedule",
        "collapse", "nowait",

        /* OpenMP-D specifics */
         "for_serialized"
    );

    /* Keywords that need values */
    private static final List<String> key_needs_value = Arrays.asList(
        "if", "num_threads", "default", "shared", "private", "firstprivate",
        "lastprivate", "reduction", "copyin", "copyprivate", "schedule",
        "collapse", "flush", "threadprivate"
    );

    /* hidden keywords : not to be printed */
    private static final List<String> hidden_keywords = Arrays.asList(
        "ompd_i_loop", "source", "bound_loop",
        "local_use_iloop", "local_def_iloop", "global_use_iloop", "hoist_loop", "ompd_loop"
    );

    /* OpenMP keywords not listed here will be printed at the end. */

    /**
     * Constructs an empty omp annotation.
     */
    public OmpdAnnotation() {
        super();
    }

    /**
     * Constructs an omp annotation with the given key-value pair.
     */
    public OmpdAnnotation(String key, Object value) {
        super();
        put(key, value);
    }

    // Prints the associated value of a directive/clause to sb.
    private void printValue(String key, StringBuilder sb) {
        Object value = get(key);
        if (value == null)
            return;
        sb.append("(");
        if (key.equals("reduction")) {
            Map<String, Set> reduction_map = get(key);
            for (String op : reduction_map.keySet()) {
                sb.append(op);
                sb.append(": ");
                sb.append(PrintTools.collectionToString(reduction_map.get(op), ", "));
            }
        }
        else if (value instanceof Collection) {
            sb.append(PrintTools.collectionToString((Collection) value, ", "));
        }
        else {
            sb.append(value.toString());
        }
        sb.append(")");
    }

    /**
     * Returns the string representation of this omp annotation.
     *
     * @return the string representation.
     */
    @Override
    public String toString() {
        if (skip_print)
            return "";

        Set<String> my_keys = new HashSet<String>(this.keySet());
        my_keys.removeAll(hidden_keywords);

        if (my_keys.isEmpty())
            return "";

        StringBuilder str = new StringBuilder(80);
        str.append(super.toString());
        str.append("ompd");

        if (my_keys.contains("score")) {
            Map<Symbol, int[]> map = get("score");
            str.append(" score");
            for (Symbol symbol : map.keySet()) {
                int [] score = map.get(symbol);
                str.append(" " + symbol.getSymbolName() + "(");
                for (int i = 0; i < score.length; i++) {
                    if (i != 0)
                        str.append(",");
                    str.append(score[i]);
                }
                str.append(")");
            }

            return str.toString();
        }

        if (my_keys.contains("total_score")) {
            Map<Expression, Integer> map = get("total_score");
            str.append(" total_score");
            for (Expression indexVariable : map.keySet()) {
                Integer score = map.get(indexVariable);
                str.append(" ");
                str.append(indexVariable);
                str.append("(" + score + ")");
            }
            return str.toString();
        }

        // Prints the directives.
        for (String key : keywords) {
            if (my_keys.contains(key)) {
                str.append(" ");
                str.append(key);
                if (key_needs_value.contains(key))
                    printValue(key, str);
                my_keys.remove(key);

                if (key.equals("barrier")){
                	str.append(" ");
                	str.append(this.get("barrier"));
                	return str.toString();
                }
                    
            }
        }
        // Remaining directives/clauses.
        for (String key : my_keys) {
            str.append(" ");
            str.append(key);
            printValue(key, str);
        }
        return str.toString();
    }

}
