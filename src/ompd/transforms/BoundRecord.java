package ompd.transforms;
 
import cetus.hir.Expression;

import java.util.HashSet;

import cetus.hir.Statement;

class BoundItem {
    Expression origLB;
    Expression origUB;
    Expression stride;
    Statement scope;
    int loopId;
    BoundItem(Expression lb, Expression ub, Expression std, int id) {
        origLB = lb.clone();
        origUB = ub.clone();
        stride = std.clone();
        loopId = id;
    }
    BoundItem(Statement Parent, Expression lb, Expression ub, Expression std, int id) {
        origLB = lb.clone();
        origUB = ub.clone();
        stride = std.clone();
        scope = Parent;
        loopId = id;
    }
}

public class BoundRecord extends HashSet<BoundItem> {

    public BoundRecord() {
        super();
    }

    void add(int loopId, Expression lb, Expression ub, Expression std) {
        BoundItem item = new BoundItem(lb, ub, std, loopId);
        add(item);
    }
    void add(int loopId, Statement scope, Expression lb, Expression ub, Expression std) {
        BoundItem item = new BoundItem(scope, lb, ub, std, loopId);
        add(item);
    }

    int getLoopId(Expression lb, Expression ub, Expression std) {
        for (BoundItem item : this) {
            if (item.origLB.equals(lb) && item.origUB.equals(ub) && item.stride.equals(std))
                return item.loopId;
        }
        return -1;
    }
    int getLoopId(Statement scope, Expression lb, Expression ub, Expression std) {
        for (BoundItem item : this) {
        	if(item.scope==null){
        		if (item.origLB.equals(lb) && item.origUB.equals(ub) && item.stride.equals(std))
                    return item.loopId;
        	}
        	else{
        		if (item.scope.equals(scope) && item.origLB.equals(lb) && item.origUB.equals(ub) && item.stride.equals(std))
                    return item.loopId;
        	}
        }
        return -1;
    }
}
