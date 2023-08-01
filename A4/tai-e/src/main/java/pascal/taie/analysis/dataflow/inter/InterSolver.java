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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        InterDataflowAnalysis<Node, Fact> ida = analysis;

        for (Node node : icfg) {
            result.setInFact(node, ida.newInitialFact());
            result.setOutFact(node, ida.newInitialFact());
        }

        Stream<Method> entryMethods = icfg.entryMethods();
        entryMethods.forEach(entryMethod -> {
            Node entryNodeOfEntryMethod = icfg.getEntryOf(entryMethod);
            result.setInFact(entryNodeOfEntryMethod, ida.newBoundaryFact(entryNodeOfEntryMethod));
            result.setOutFact(entryNodeOfEntryMethod, ida.newBoundaryFact(entryNodeOfEntryMethod));
        });

    }

    private void doSolve() {
        // TODO - finish me
        InterDataflowAnalysis<Node, Fact> ida = analysis;

        Set<Node> entryAndExitNodeOfEntryMethods = new HashSet<>();
        Stream<Method> entryMethods = icfg.entryMethods();
        entryMethods.forEach(entryMethod -> {
            entryAndExitNodeOfEntryMethods.add(icfg.getEntryOf(entryMethod));
            entryAndExitNodeOfEntryMethods.add(icfg.getExitOf(entryMethod));
        });

        List<Node> workList = new ArrayList<>();
        for (Node node : icfg.getNodes()) {      // cfg.getNodes() will return all statements of a function
            if(!(entryAndExitNodeOfEntryMethods.contains(node))) {
                workList.add(node);
            }
        }

        while(workList.size() > 0) {
            Node node = workList.get(0);
            Fact newIn = ida.newInitialFact();

            // calculate the new InFact
            Set<Node> preNodes = icfg.getPredsOf(node);
            Set<ICFGEdge<Node>> preEdges = icfg.getInEdgesOf(node);

            if (node.toString().equals("temp$5 = temp$1 + temp$4")) {
                int a = 1;
            }
            if (node.toString().equals("%intconst2 = 2")) {
                int b = 2;
            }

            for(int i = 0; i < preNodes.size(); i++) {
                Node preNode = preNodes.stream().toList().get(i);
                ICFGEdge<Node> preEdge = preEdges.stream().toList().get(i);

                Fact transferredFact = ida.transferEdge(preEdge, result.getOutFact(preNode));
                if (transferredFact != null) {
                    ida.meetInto(transferredFact, newIn);
                } else {
                    int a = 1;
                }
            }

            // get the new InFact
            result.setInFact(node, newIn);

            // handle certain node, input the InFact and will give out the OutFact
            boolean anyChange = ida.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(anyChange) {
                workList.addAll(icfg.getSuccsOf(node));
            }

            workList.remove(node);
        }
    }
}
