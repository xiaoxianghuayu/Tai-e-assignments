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

import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Pair;
import org.yaml.snakeyaml.events.AliasEvent;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    // new field
    public static Map<Var, Set<Var>> aliasMap = new HashMap<>();
    public static Map<Pair<?, ?>, Value> varValueMap = new HashMap<>();
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticLoadFieldStmtMap = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        for (Var var1: pta.getVars()) {
            for (Var var2: pta.getVars()) {
                // exists overlap
                for (Obj basePtr: pta.getPointsToSet(var1)) {
                    if (pta.getPointsToSet(var2).contains(basePtr)) {
                        // add var2 to var1's Alias Set(including var1 itself)
                        Set<Var> varList = aliasMap.getOrDefault(var1, new HashSet<>());
                        if (!varList.contains(var2)) {
                            varList.add(var2);
                            aliasMap.put(var1, varList);
                        }
                    }
                }
            }
        }

        for (Stmt stmt : icfg.getNodes()) {
            if (stmt instanceof LoadField loadField && loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                Pair<JClass, FieldRef> mapKey = new Pair<>(loadField.getFieldRef().getDeclaringClass(), loadField.getFieldRef());

                Set<LoadField> tmpSet = staticLoadFieldStmtMap.getOrDefault(mapKey, new HashSet<>());
                tmpSet.add(loadField);
                staticLoadFieldStmtMap.put(mapKey, tmpSet);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean anyChanged = cp.transferNode(stmt, in, out);

        Optional<LValue> stmtDef = stmt.getDef();
        // TODO:: 需要做进一步分析
        if (stmtDef.isPresent() && stmtDef.get() instanceof Var lValue) {
            out.remove(lValue);
        }
        return anyChanged;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact newFact = new CPFact();
        newFact.copyFrom(out);

        return newFact;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        CPFact newFact = new CPFact();
        newFact.copyFrom(out);

        Optional<LValue> newDef = edge.getSource().getDef();
        if (newDef.isPresent()) {
            LValue lValue = edge.getSource().getDef().get();
            if (lValue instanceof Var) {
                newFact.remove((Var) lValue);
            }
        }

        return newFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        CPFact newFact = new CPFact();

        List<Var> callerArgs = ((Invoke) edge.getSource()).getInvokeExp().getArgs();
        List<Var> calleeParams = edge.getCallee().getIR().getParams();

        for (int i = 0; i < calleeParams.size(); i++) {
            Var arg = callerArgs.get(i);
            Var param = calleeParams.get(i);

            newFact.update(param, callSiteOut.get(arg));
        }
        return newFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me

        CPFact newFact = new CPFact();

        Var returnDef = ((Invoke) ((ReturnEdge) edge).getCallSite()).getLValue();
        if (!edge.getReturnVars().isEmpty() && returnDef != null) {

            Collection<Var> returnVars = edge.getReturnVars();

            if (returnVars.size() == 1) {
                Var returnVar = returnVars.stream().toList().get(0);
                newFact.update(returnDef, returnOut.get(returnVar));
            } else {
                // TODO::NOT ACCURATE
                newFact.update(returnDef, Value.getNAC());
            }

            return newFact;
        }

        return null;
    }
}
