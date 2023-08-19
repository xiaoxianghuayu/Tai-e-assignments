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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public Set<CSCallSite> sinkInvoke = new HashSet<>();
    public Set<Invoke> sourceInvoke = new HashSet<>();

    private final Set<JMethod> baseToResult = new HashSet<>();
    private final Set<JMethod> argToBase = new HashSet<>();
    private final Set<JMethod> argToResult = new HashSet<>();


    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);


        loadTransferFunctions();
    }

    // TODO - finish
    private void loadTransferFunctions() {
        for(TaintTransfer taintTransfer: config.getTransfers()) {
            JMethod method = taintTransfer.method();
            int from = taintTransfer.from();
            int to = taintTransfer.to();

            // base: -1, result: -2
            if (from == -1 && to == -2) {
                baseToResult.add(method);
            } else if (from >= 0 && to == -2) {
                argToResult.add(method);
            } else if (from >= 0 && to == -1) {
                argToBase.add(method);
            }
        }
    }

    public boolean isBaseToResult(JMethod method) {
        return baseToResult.contains(method);
    }

    public boolean isArgToResult(JMethod method) {
        return argToResult.contains(method);
    }
    public boolean isArgToBase(JMethod method) {
        return argToBase.contains(method);
    }

    public boolean inSourceSet(JMethod method, Type type) {
        return config.getSources().contains(new Source(method, type));
    }

    public boolean inSinkSet(JMethod method, int index) {
        return config.getSinks().contains(new Sink(method, index));
    }

    public int getSinkArgIndex(JMethod method) {
        for (int i = 0; i < method.getParamCount(); i++) {
            if (inSinkSet(method, i)) {
                return i;
            }
        }
        return -1;
    }

    public Obj makeTaintObj(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public boolean isTaintObj(Obj obj) {
        return manager.isTaint(obj);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        for(CSCallSite csInvoke: sinkInvoke) {
            Invoke invoke = csInvoke.getCallSite();
            Context context = csInvoke.getContext();

            int sinkArgIndex = getSinkArgIndex(invoke.getInvokeExp().getMethodRef().resolve());

            CSVar csVar = csManager.getCSVar(context, invoke.getInvokeExp().getArg(sinkArgIndex));
            for(CSObj csObj: csVar.getPointsToSet()) {
                Obj obj = csObj.getObject();
                if (manager.isTaint(obj)) {
                    TaintFlow taintFlow = new TaintFlow(manager.getSourceCall(obj), invoke, sinkArgIndex);
                    taintFlows.add(taintFlow);
                }
            }
        }

        return taintFlows;
    }
}
