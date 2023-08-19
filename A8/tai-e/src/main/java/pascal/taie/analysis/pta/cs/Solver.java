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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);

            List<Stmt> methodStmts = csMethod.getMethod().getIR().getStmts();
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for(Stmt stmt: methodStmts) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // x = new T()
            Var leftVar = stmt.getLValue();
            Obj leftObj = heapModel.getObj(stmt);

            CSVar csVarPtr = csManager.getCSVar(this.context, leftVar);
            Context heapContext = contextSelector.selectHeapContext(this.csMethod, leftObj);
            CSObj csObj = csManager.getCSObj(heapContext, leftObj);

            PointsToSet newPointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(csVarPtr, newPointsToSet);

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            CSVar xCSVar = csManager.getCSVar(this.context, x);
            CSVar yCSVar = csManager.getCSVar(this.context, y);

            addPFGEdge(yCSVar, xCSVar);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.getInvokeExp() instanceof InvokeStatic invokeStaticStmt) {
                JMethod targetMethod = invokeStaticStmt.getMethodRef().resolve();

                Context c = this.context;
                CSCallSite csCallSite = csManager.getCSCallSite(c, stmt);
                Context ct = contextSelector.selectContext(csCallSite, targetMethod);

                CSMethod targetCSMethod = csManager.getCSMethod(ct, targetMethod);
                addReachable(targetCSMethod);

                Edge<CSCallSite, CSMethod> newEdge = new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, targetCSMethod);
                callGraph.addEdge(newEdge);

                handleArgAndRet(stmt, c, targetMethod, ct);
            }

            // Taint: sink() and source() are both static
            if (stmt.getInvokeExp() instanceof InvokeStatic invokeStaticStmt) {
                JMethod currentMethod = invokeStaticStmt.getMethodRef().resolve();
                Type retType = invokeStaticStmt.getType();
                if (taintAnalysis.inSourceSet(currentMethod, retType)) {
                    taintAnalysis.sourceInvoke.add(stmt);

                    Context emptyContext = contextSelector.getEmptyContext();
                    Obj newTaintObj = taintAnalysis.makeTaintObj(stmt, retType);
                    CSObj newCSTaintObj = csManager.getCSObj(emptyContext, newTaintObj);

                    Var left = stmt.getResult();
                    if (left != null) {
                        csManager.getCSVar(emptyContext, left).getPointsToSet().addObject(newCSTaintObj);
//                        workList.addEntry(csManager.getCSVar(emptyContext, left), PointsToSetFactory.make(newCSTaintObj));
                    }
                } else if (taintAnalysis.getSinkArgIndex(currentMethod) != -1) {
                    taintAnalysis.sinkInvoke.add(csManager.getCSCallSite(this.context, stmt));
                }
            }

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                CSVar leftVarPointer = csManager.getCSVar(this.context, stmt.getLValue());

                FieldAccess right = stmt.getFieldAccess();
                JField rightStaticField = right.getFieldRef().resolve();
                StaticField rightStaticFieldPointer = csManager.getStaticField(rightStaticField);

                addPFGEdge(rightStaticFieldPointer, leftVarPointer);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                CSVar rightVarPointer = csManager.getCSVar(this.context, stmt.getRValue());

                FieldAccess left = stmt.getFieldAccess();
                JField leftStaticField = left.getFieldRef().resolve();
                StaticField leftStaticFieldPointer = csManager.getStaticField(leftStaticField);

                addPFGEdge(rightVarPointer, leftStaticFieldPointer);
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
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pt = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet delta = propagate(pt, pts);
            if (pt instanceof CSVar csVar) {
                Var x = csVar.getVar();
                Context c = csVar.getContext();
                for (CSObj csObj: delta) {
                    for(StoreField stmt: x.getStoreFields()) {
                        // x.f = y
                        CSVar yCSVar = csManager.getCSVar(c, stmt.getRValue());

                        FieldAccess left = stmt.getFieldAccess();
                        Var leftBase = ((InstanceFieldAccess) left).getBase();
                        for(CSObj leftCSObj: csManager.getCSVar(c, leftBase).getPointsToSet()) {
                            InstanceField leftInstancePointer = csManager.getInstanceField(leftCSObj, left.getFieldRef().resolve());

                            addPFGEdge(yCSVar, leftInstancePointer);
                        }
                    }

                    for(LoadField stmt: x.getLoadFields()) {
                        // y = x.f
                        CSVar yCSVar = csManager.getCSVar(c, stmt.getLValue());

                        FieldAccess right = stmt.getFieldAccess();
                        Var rightBase = ((InstanceFieldAccess) right).getBase();
                        for(CSObj rightCSObj: csManager.getCSVar(c, rightBase).getPointsToSet()) {
                            InstanceField rightInstancePointer = csManager.getInstanceField(rightCSObj, right.getFieldRef().resolve());

                            addPFGEdge(rightInstancePointer, yCSVar);
                        }
                    }

                    for (StoreArray storeArrayStmt: x.getStoreArrays()) {
                        // x[i] = y
                        CSVar xCSVar = csManager.getCSVar(c, storeArrayStmt.getLValue().getBase());
                        CSVar yCSVar = csManager.getCSVar(c, storeArrayStmt.getRValue());

                        for(CSObj leftCSObj: xCSVar.getPointsToSet()) {
                            ArrayIndex arrayIndexPointer = csManager.getArrayIndex(leftCSObj);

                            addPFGEdge(yCSVar, arrayIndexPointer);
                        }
                    }

                    for (LoadArray loadArrayStmt: x.getLoadArrays()) {
                        // y = x[i]
                        CSVar yCSVar = csManager.getCSVar(c, loadArrayStmt.getLValue());
                        CSVar xCSVar = csManager.getCSVar(c, loadArrayStmt.getRValue().getBase());

                        for(CSObj rightCSObj: xCSVar.getPointsToSet()) {
                            ArrayIndex arrayIndexPointer = csManager.getArrayIndex(rightCSObj);
                            addPFGEdge(arrayIndexPointer, yCSVar);
                        }
                    }

                    processCall(csVar, csObj);
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

        PointsToSet delta = PointsToSetFactory.make();

        PointsToSet ptn = pointer.getPointsToSet();
        for(CSObj csObj: pointsToSet) {
            if (!ptn.contains(csObj)) {
                delta.addObject(csObj);
            }
        }

        if (!delta.isEmpty()) {
            for(CSObj csObj: delta) {
                ptn.addObject(csObj);
            }
            for (Pointer sucPointer: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(sucPointer, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context c = recv.getContext();
        Var var = recv.getVar();
        Obj varObj = recvObj.getObject();

        // recv taint as arg
        if (taintAnalysis.isTaintObj(varObj)) {
            for(CSMethod csMethod: callGraph.reachableMethods().toList()) {
                if (!csMethod.getContext().equals(c)) {
                    continue;
                }
                for(Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
                    if (stmt instanceof Invoke invoke) {
                        for(Var arg: invoke.getInvokeExp().getArgs()) {
                            if (var.equals(arg)) {
                                JMethod method = invoke.getMethodRef().resolve();

                                // argToResult example: String s2 = s1.concat(taint);
                                if (!invoke.isStatic() && taintAnalysis.isArgToBase(method)) {
                                    Var base = ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
                                    CSVar csBase = csManager.getCSVar(c, base);
                                    workList.addEntry(csBase, PointsToSetFactory.make(recvObj));
                                }
                                // argToBase example: sb.append(taint);
                                if (taintAnalysis.isArgToResult(method)) {
                                    Var result = invoke.getLValue();
                                    CSVar csResult = csManager.getCSVar(c, result);
                                    workList.addEntry(csResult, PointsToSetFactory.make(recvObj));
                                }
                            }
                        }
                    }
                }
            }
        }


        for(Invoke invokeStmt: var.getInvokes()) {
            // recv taint as base
            if (taintAnalysis.isTaintObj(varObj)) {
                // baseToResult example:  String s2 = taint.concat(s1);
                if (!invokeStmt.isStatic() && taintAnalysis.isBaseToResult(invokeStmt.getMethodRef().resolve())) {
                    CSVar csResult = csManager.getCSVar(c, invokeStmt.getLValue());
                    workList.addEntry(csResult, PointsToSetFactory.make(recvObj));
                }
                continue;
            }

            JMethod targetMethod = resolveCallee(recvObj, invokeStmt);

            // the csCallSiteContext includes the context and the line number of the call site
            CSCallSite csCallSite = csManager.getCSCallSite(c, invokeStmt);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, null);

            // handle `this`
            CSVar thisCSVar = csManager.getCSVar(ct, targetMethod.getIR().getThis());
            PointsToSet newPointsToSet = PointsToSetFactory.make(recvObj);
            workList.addEntry(thisCSVar, newPointsToSet);

            CSMethod targetCSMethod = csManager.getCSMethod(ct, targetMethod);
            Edge<CSCallSite, CSMethod> newEdge = new Edge<>(CallGraphs.getCallKind(invokeStmt), csCallSite, targetCSMethod);
            if (!callGraph.edgesOutOf(csCallSite).toList().contains(newEdge)) {
                callGraph.addEdge(newEdge);
                addReachable(targetCSMethod);

                handleArgAndRet(invokeStmt, c, targetMethod, ct);
            }
        }
    }

    private void handleArgAndRet(Invoke invokeStmt, Context c, JMethod targetMethod, Context ct) {
        List<Var> args = invokeStmt.getInvokeExp().getArgs();
        List<Var> params = targetMethod.getIR().getParams();

        List<Var> rets = targetMethod.getIR().getReturnVars();
        Var receiver = invokeStmt.getResult();

        for (int i = 0; i < params.size(); i++) {
            Var arg = args.get(i);
            Var param = params.get(i);
            addPFGEdge(csManager.getCSVar(c, arg), csManager.getCSVar(ct, param));
        }
        if (receiver != null) {
            for(Var ret: rets) {
                addPFGEdge(csManager.getCSVar(ct, ret), csManager.getCSVar(c, receiver));
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
