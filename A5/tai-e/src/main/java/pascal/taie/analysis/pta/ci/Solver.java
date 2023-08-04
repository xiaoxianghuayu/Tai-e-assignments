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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import javax.swing.text.html.Option;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        /* traditional method
        if(!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);

            List<Stmt> methodStmts = method.getIR().getStmts();
            for(Stmt stmt: methodStmts) {
                if (stmt instanceof New newStmt) {
                    // i: x = new T()
                    // TODO::处理左边变量不是 Var 的情况?
                    LValue x = newStmt.getLValue();
                    VarPtr xVarPtr = pointerFlowGraph.getVarPtr((Var) x);   // create a VarPtr that represent the `x` which is in fact a Pointer.
                    PointsToSet newPointsToSet = new PointsToSet(heapModel.getObj(newStmt));  // the created VarPtr has its pt(n)

                    workList.addEntry(xVarPtr, newPointsToSet);
                }

                // the definition stmt always before the use stmt
                if (stmt instanceof Copy copyStmt) {
                    // x = y
                    LValue x = copyStmt.getLValue();
                    RValue y = copyStmt.getRValue();
                    VarPtr xVarPtr = pointerFlowGraph.getVarPtr((Var) x);
                    VarPtr yVarPtr = pointerFlowGraph.getVarPtr((Var) y);

                    addPFGEdge(yVarPtr, xVarPtr);
                }

                if (stmt instanceof Invoke invokeStmt) {

                    // invokestatic is like: temp$0 = invokestatic A.foo(), so it should be handled there
                    if (invokeStmt.getInvokeExp() instanceof InvokeStatic invokeStaticStmt) {
                        JMethod targetMethod = invokeStaticStmt.getMethodRef().resolve();

                        // TODO::更新全局可访问stmts?
                        addReachable(targetMethod);

                        List<Var> args = invokeStaticStmt.getArgs();
                        List<Var> params = targetMethod.getIR().getParams();
                        for (int i = 0; i < params.size(); i++) {
                            Var arg = args.get(i);
                            Var param = params.get(i);
                            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                        }

                        Var receiver = invokeStmt.getResult();
                        if (receiver != null) {
                            List<Var> rets = targetMethod.getIR().getReturnVars();
                            for(Var ret: rets) {
                                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(receiver));
                            }
                        }
                    }
                    // TODO:: 其他invoke情况?
                }

                if (stmt instanceof StoreField storeFieldStmt) {
                    if (storeFieldStmt.isStatic()) {
                        // T.x = y;
                        VarPtr rightVarPointer = pointerFlowGraph.getVarPtr(storeFieldStmt.getRValue());

                        FieldAccess left = storeFieldStmt.getFieldAccess();
                        JField leftStaticField = left.getFieldRef().resolve();
                        StaticField leftStaticFieldPointer = pointerFlowGraph.getStaticField(leftStaticField);

                        addPFGEdge(rightVarPointer, leftStaticFieldPointer);
                    }
                }

                if (stmt instanceof LoadField loadFieldStmt) {
                    if (loadFieldStmt.isStatic()) {
                        // y = T.x
                        VarPtr leftVarPointer = pointerFlowGraph.getVarPtr(loadFieldStmt.getLValue());

                        FieldAccess right = loadFieldStmt.getFieldAccess();
                        JField rightStaticField = right.getFieldRef().resolve();
                        StaticField rightStaticFieldPointer = pointerFlowGraph.getStaticField(rightStaticField);

                        addPFGEdge(rightStaticFieldPointer, leftVarPointer);

                    }
                }
            }

        }
        */

        // visitor pattern
        if(!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);

            List<Stmt> methodStmts = method.getIR().getStmts();
            for(Stmt stmt: methodStmts) {
                stmt.accept(stmtProcessor);
            }
        }

    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            New newStmt = stmt;
            LValue x = newStmt.getLValue();
            VarPtr xVarPtr = pointerFlowGraph.getVarPtr((Var) x);   // create a VarPtr that represent the `x` which is in fact a Pointer.
            PointsToSet newPointsToSet = new PointsToSet(heapModel.getObj(newStmt));  // the created VarPtr has its pt(n)

            workList.addEntry(xVarPtr, newPointsToSet);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            Copy copyStmt = stmt;
            LValue x = copyStmt.getLValue();
            RValue y = copyStmt.getRValue();
            VarPtr xVarPtr = pointerFlowGraph.getVarPtr((Var) x);
            VarPtr yVarPtr = pointerFlowGraph.getVarPtr((Var) y);

            addPFGEdge(yVarPtr, xVarPtr);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            Invoke invokeStmt = stmt;
            if (invokeStmt.getInvokeExp() instanceof InvokeStatic invokeStaticStmt) {
                JMethod targetMethod = invokeStaticStmt.getMethodRef().resolve();

                addReachable(targetMethod);

                List<Var> args = invokeStaticStmt.getArgs();
                List<Var> params = targetMethod.getIR().getParams();
                for (int i = 0; i < params.size(); i++) {
                    Var arg = args.get(i);
                    Var param = params.get(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                }

                Var receiver = invokeStmt.getResult();
                if (receiver != null) {
                    List<Var> rets = targetMethod.getIR().getReturnVars();
                    for(Var ret: rets) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(receiver));
                    }
                }
            }

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            StoreField storeFieldStmt = stmt;
            if (storeFieldStmt.isStatic()) {
                VarPtr rightVarPointer = pointerFlowGraph.getVarPtr(storeFieldStmt.getRValue());

                FieldAccess left = storeFieldStmt.getFieldAccess();
                JField leftStaticField = left.getFieldRef().resolve();
                StaticField leftStaticFieldPointer = pointerFlowGraph.getStaticField(leftStaticField);

                addPFGEdge(rightVarPointer, leftStaticFieldPointer);
            }

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            LoadField loadFieldStmt = stmt;
            if (loadFieldStmt.isStatic()) {
                // y = T.x
                VarPtr leftVarPointer = pointerFlowGraph.getVarPtr(loadFieldStmt.getLValue());

                FieldAccess right = loadFieldStmt.getFieldAccess();
                JField rightStaticField = right.getFieldRef().resolve();
                StaticField rightStaticFieldPointer = pointerFlowGraph.getStaticField(rightStaticField);

                addPFGEdge(rightStaticFieldPointer, leftVarPointer);

            }

            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me

        List<Stmt> totalReachableStmts = new ArrayList<>();
        for(JMethod entryMethod: callGraph.entryMethods().toList()) {
            totalReachableStmts.addAll(entryMethod.getIR().getStmts());
        }

        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pt = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet delta = propagate(pt, pts);


            if (pt instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                for(Obj obj: delta) {
                    for(StoreField stmt: x.getStoreFields()) {
                        // x.f = y
                        // TODO:: 如果其他地方无法添加, 那么这个地方也不能检查
                        if (true || totalReachableStmts.contains(stmt)) {
                            VarPtr rightVarPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());

                            FieldAccess left = stmt.getFieldAccess();
                            Var leftBase = ((InstanceFieldAccess) left).getBase();
                            for(Obj obj1: pointerFlowGraph.getVarPtr(leftBase).getPointsToSet()) {
                                InstanceField leftInstancePointer = pointerFlowGraph.getInstanceField(obj1, left.getFieldRef().resolve());

                                addPFGEdge(rightVarPtr, leftInstancePointer);
                            }
                        }
                    }

                    for(LoadField stmt: x.getLoadFields()) {
                        // y = x.f
                        if (true || totalReachableStmts.contains(stmt)) {
                            VarPtr leftVarPointer = pointerFlowGraph.getVarPtr(stmt.getLValue());

                            FieldAccess right = stmt.getFieldAccess();
                            Var rightBase = ((InstanceFieldAccess) right).getBase();
                            for(Obj obj1: pointerFlowGraph.getVarPtr(rightBase).getPointsToSet()) {
                                InstanceField rightInstancePointer = pointerFlowGraph.getInstanceField(obj1, right.getFieldRef().resolve());

                                addPFGEdge(rightInstancePointer, leftVarPointer);
                            }
                        }
                    }

                    processCall(x, obj);


                    for (StoreArray storeArrayStmt: x.getStoreArrays()) {
                        // x[i] = y
                        VarPtr leftVarPointer = pointerFlowGraph.getVarPtr(storeArrayStmt.getLValue().getBase());
                        VarPtr rightVarPointer = pointerFlowGraph.getVarPtr(storeArrayStmt.getRValue());

                        for(Obj obj1: leftVarPointer.getPointsToSet()) {
                            ArrayIndex arrayIndexPointer = pointerFlowGraph.getArrayIndex(obj1);
                            addPFGEdge(rightVarPointer, arrayIndexPointer);
                        }
                    }

                    for (LoadArray loadArrayStmt: x.getLoadArrays()) {
                        // y = x[i]
                        VarPtr leftVarPointer = pointerFlowGraph.getVarPtr(loadArrayStmt.getLValue());
                        VarPtr rightVarPointer = pointerFlowGraph.getVarPtr(loadArrayStmt.getRValue().getBase());

                        for(Obj obj1: rightVarPointer.getPointsToSet()) {
                            ArrayIndex arrayIndexPointer = pointerFlowGraph.getArrayIndex(obj1);
                            addPFGEdge(arrayIndexPointer, leftVarPointer);
                        }
                    }
                }
            }
        }


    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();

        PointsToSet pts = pointsToSet;
        PointsToSet ptn = pointer.getPointsToSet();
        for(Obj obj: pts) {
            if (!ptn.contains(obj)) {       // ptr that in pts but not in pt(n)
                delta.addObject(obj);

//                ptn.addObject(obj);         // the new added ptr merge into pt(n)
            }
        }

        if (!delta.isEmpty()) {
            for(Obj obj: delta) {
                ptn.addObject(obj);
            }
            for (Pointer sucPointer: pointerFlowGraph.getSuccsOf(pointer)) {    // handle the succ node
                workList.addEntry(sucPointer, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me

        // handle x.m()
        for(Invoke invokeStmt: var.getInvokes()) {
            // TODO:: 检查invokeStmt是否在可访问的stmts里?

            JMethod targetMethod = resolveCallee(recv, invokeStmt);

            VarPtr thisVarPtr = pointerFlowGraph.getVarPtr(targetMethod.getIR().getThis());
            PointsToSet newPointsToSet = new PointsToSet(recv);
            workList.addEntry(thisVarPtr, newPointsToSet);

            Edge<Invoke, JMethod> newEdge = new Edge<>(CallGraphs.getCallKind(invokeStmt), invokeStmt, targetMethod);
            if (!callGraph.edgesOutOf(invokeStmt).toList().contains(newEdge)) {
                callGraph.addEdge(newEdge);
                
                // TODO::更新全局可访问stmts?
                addReachable(targetMethod);

                List<Var> args = invokeStmt.getInvokeExp().getArgs();
                List<Var> params = targetMethod.getIR().getParams();
                for (int i = 0; i < params.size(); i++) {
                    Var arg = args.get(i);
                    Var param = params.get(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                }

                List<Var> rets = targetMethod.getIR().getReturnVars();
                Var receiver = invokeStmt.getResult();
                if (receiver != null) {
                    for(Var ret: rets) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(receiver));
                    }
                }

            }
        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
