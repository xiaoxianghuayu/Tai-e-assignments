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
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
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

    public static Set<Sink> sinkSet;
    public static Set<Source> sourceSet;
    public static Set<TaintTransfer> taintTransferSet;

    public Set<CSCallSite> sinkInvoke = new HashSet<>();
    public Set<Invoke> sourceInvoke = new HashSet<>();

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


        sinkSet = config.getSinks();
        sourceSet = config.getSources();
        taintTransferSet = config.getTransfers();
    }

    // TODO - finish
    public boolean inTaintTransfer(JMethod method, int from, int to, Type type) {
        return taintTransferSet.contains(new TaintTransfer(method, from, to, type));
    }

    public int getTaintTransferBaseToResultArgIndex(JMethod method, Type type) {
        return inTaintTransfer(method, -1, -2, type) ? 1 : -1;      // base to result do not need arg, 1 represent "in" and -1 represents "not in"
    }
    public int getTaintTransferArgToBaseArgIndex(JMethod method, Type type) {
        for (int i = 0; i < method.getParamCount(); i++) {
            if (inTaintTransfer(method, i, -1, type)) {
                return i;
            }
        }
        return -1;
    }

    public int getTaintTransferArgToResultArgIndex(JMethod method, Type type) {
        for (int i = 0; i < method.getParamCount(); i++) {
            if (inTaintTransfer(method, i, -2, type)) {
                return i;
            }
        }
        return -1;
    }

    public boolean inSourceSet(JMethod method, Type type) {
        return sourceSet.contains(new Source(method, type));
    }

    public boolean inSinkSet(JMethod method, int index) {
        return sinkSet.contains(new Sink(method, index));
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

    public Invoke getTaintSourceCall(Obj obj) {
        return manager.getSourceCall(obj);
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
