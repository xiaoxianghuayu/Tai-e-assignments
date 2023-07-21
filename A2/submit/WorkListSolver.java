/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        DataflowAnalysis<Node, Fact> cpa = analysis;

        List<Node> workList = new ArrayList<>();
        for (Node node : cfg.getNodes()) {      // cfg.getNodes() will return all statements of a function
            if(!(cfg.isEntry(node) || cfg.isExit(node))) {
                workList.add(node);
            }
        }

        while(workList.size() > 0) {
            Node node = workList.get(0);
            Fact newIn = cpa.newInitialFact();

            for(Node preNode: cfg.getPredsOf(node)) {
                // newIn could be replaced by `result.getInFact(preNode)`, the original var,
                // because in `IN[B] = U OUT[P]`, the OUT[P] is monotonically increasing, so even the newIn is not empty,
                // the old value is must smaller than the new value, so it is no problem.
                cpa.meetInto(result.getOutFact(preNode), newIn);
            }
            result.setInFact(node, newIn);

            boolean anyChange = cpa.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(anyChange) {
                workList.addAll(cfg.getSuccsOf(node));
            }

            workList.remove(node);
        }
//        System.out.println("1111");
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
