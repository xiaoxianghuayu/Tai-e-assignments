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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Stream;


import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.meetValue;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;

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

        workList = new SetQueue<>();
        for (Node node : icfg.getNodes()) {      // cfg.getNodes() will return all statements of a function
            if(!(entryAndExitNodeOfEntryMethods.contains(node))) {
                workList.add(node);
            }
        }

        while(!workList.isEmpty()) {
            Node node = workList.poll();
            Fact newIn = ida.newInitialFact();

            // calculate the new InFact
            Set<Node> preNodes = icfg.getPredsOf(node);
            Set<ICFGEdge<Node>> preEdges = icfg.getInEdgesOf(node);

            if (node.toString().equals("y = a2.<A: int f>")) {
                int a = 1;
            }

            for(int i = 0; i < preNodes.size(); i++) {
                Node preNode = preNodes.stream().toList().get(i);
                ICFGEdge<Node> preEdge = preEdges.stream().toList().get(i);

                Fact transferredFact = ida.transferEdge(preEdge, result.getOutFact(preNode));
                if (transferredFact != null) {
                    ida.meetInto(transferredFact, newIn);
                }
            }

            // get the new InFact
            result.setInFact(node, newIn);

            // handle store
            handleStoreStmt(node, (CPFact) result.getInFact(node));

            // handle certain node, input the InFact and will give out the OutFact
            boolean anyChange = ida.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(anyChange) {
                workList.addAll(icfg.getSuccsOf(node));
            }

        }
    }

    private void handleStoreStmt(Node stmt, CPFact in) {
        if (stmt instanceof StoreField storeFieldStmt) {
            handleStoreField(storeFieldStmt, in);
        } else if (stmt instanceof StoreArray storeArrayStmt) {
            handleStoreArray(storeArrayStmt, in);
        }
    }

    private void handleStoreField(StoreField storeFieldStmt, CPFact in) {
        // x.f = y
//        if (!ConstantPropagation.canHoldInt(storeFieldStmt.getRValue())) { return; }
        if (storeFieldStmt.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
            Var base = instanceFieldAccess.getBase();

            for (Obj obj : ptaResult.getPointsToSet(base)) {
                Pair<Obj, FieldRef> mapKey = new Pair<>(obj, storeFieldStmt.getFieldRef());
                Value oldValue = varMap.getOrDefault(mapKey, Value.getUndef());
                Value newValue = ConstantPropagation.evaluate(storeFieldStmt.getRValue(), in);
                newValue = meetValue(oldValue, newValue);

                varMap.put(mapKey, newValue);

                if (!oldValue.equals(newValue)) {
                    Set<Var> aliases = aliasMap.get(obj);
                    aliases.forEach(alias -> {
                        for(LoadField loadFieldStmt: alias.getLoadFields()) {
                            if (loadFieldStmt.getFieldRef().equals(storeFieldStmt.getFieldRef())) {
                                workList.offer((Node) loadFieldStmt);
                            }
                        }
                    });
                }
            }
        } else if (storeFieldStmt.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
            JClass clz = storeFieldStmt.getFieldRef().getDeclaringClass();
            Pair<JClass, FieldRef> mapKey = new Pair<>(clz, storeFieldStmt.getFieldRef());
            Value oldValue = varMap.getOrDefault(mapKey, Value.getUndef());
            Value newValue = ConstantPropagation.evaluate(storeFieldStmt.getRValue(), in);
            newValue = meetValue(oldValue, newValue);

            varMap.put(mapKey, newValue);

            staticLoadFieldStmtMap.get(mapKey).forEach(staticLoadFieldStmt -> {
                workList.offer((Node) staticLoadFieldStmt);
            });
        }
    }

    private void handleStoreArray(StoreArray storeArrayStmt, CPFact in) {
        // a[i] = x
//        if(!ConstantPropagation.canHoldInt(s.getRValue())) return;

        ArrayAccess storeArrayAccess = storeArrayStmt.getArrayAccess();
        Var base = storeArrayAccess.getBase();
        Value index = ConstantPropagation.evaluate(storeArrayAccess.getIndex(), in);
        // no alias, no effect on other stmt
        if (index.isUndef()) return;

        for (Obj obj: ptaResult.getPointsToSet(base)) {
            Pair<Obj, Value> mapKey = new Pair<>(obj, index);
            Value oldValue = varMap.getOrDefault(mapKey, Value.getUndef());
            Value newValue = ConstantPropagation.evaluate(storeArrayStmt.getRValue(), in);
            newValue = meetValue(oldValue, newValue);

            varMap.put(mapKey, newValue);
            if (!oldValue.equals(newValue)) {
                Set<Var> aliases = aliasMap.get(obj);
                aliases.forEach(alias -> {
                    for(LoadArray loadArrayStmt: alias.getLoadArrays()) {
                        workList.offer((Node) loadArrayStmt);
                    }
                });
            }
        }
    }
}
