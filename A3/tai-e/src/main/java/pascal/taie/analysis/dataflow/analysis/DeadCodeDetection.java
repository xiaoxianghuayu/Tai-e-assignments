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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Set<Stmt> reachableCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        List<Stmt> stmtList = new ArrayList<>();

        stmtList.add(cfg.getEntry());
        while (stmtList.size() > 0) {
            Stmt curStmt = stmtList.get(0);
            stmtList.remove(curStmt);
            if (reachableCode.contains(curStmt)) {
                continue;
            }
            reachableCode.add(curStmt);

            // dead assignment only appears in AssignStmt
            if (curStmt instanceof AssignStmt<?,?> assignStmt) {
                LValue left = assignStmt.getLValue();
                RValue right = assignStmt.getRValue();
                if (left instanceof Var && !liveVars.getOutFact(curStmt).contains((Var) left)) {
                    // left is Var but not a live Var
                    if (hasNoSideEffect(right)) {      // this stm has no side effect, mark it as unreachable. i.e. will be removed later
                        reachableCode.remove(curStmt);
                    }
                }

            }


            // select next edge
            // CAUGHT_EXCEPTION  UNCAUGHT_EXCEPTION
            Set<Edge<Stmt>> nextEdges = cfg.getOutEdgesOf(curStmt);
            // only one out edge: FALL_THROUGH, GOTO, ENTRY
            if (nextEdges.size() == 1) {
                Stmt target = nextEdges.iterator().next().getTarget();
                stmtList.add(target);
            } else {
                // just 0 edge: RETURN
                // more than one edge: IF_TRUE/IF_FALSE, SWITCH_CASE/SWITCH_DEFAULT
                if (curStmt instanceof If) {
                    Edge<Stmt> trueEdge = null;
                    Edge<Stmt> falseEdge = null;
                    for (Edge <Stmt> tmpStmt: nextEdges) {
                        if (tmpStmt.getKind() == Edge.Kind.IF_TRUE) {
                            trueEdge = tmpStmt;
                        } else if (tmpStmt.getKind() == Edge.Kind.IF_FALSE) {
                            falseEdge = tmpStmt;
                        }
                    }

                    ConditionExp conditionExp = ((If) curStmt).getCondition();
                    Value conditionExpResult = ConstantPropagation.evaluate(conditionExp, constants.getInFact(curStmt));
                    // if the condition is fixed
                    if (conditionExpResult.isConstant()) {
                        int realValue = conditionExpResult.getConstant();
                        if (realValue > 0) {
                            stmtList.add(trueEdge.getTarget());
                        } else {
                            stmtList.add(falseEdge.getTarget());
                        }
                    } else {
                        stmtList.add(trueEdge.getTarget());
                        stmtList.add(falseEdge.getTarget());
                    }
                } else if(curStmt instanceof SwitchStmt) {
                    Var switchVar = ((SwitchStmt) curStmt).getVar();
                    Value switchValue = constants.getInFact(curStmt).get(switchVar);
                    if (switchValue.isConstant()) {
                        int realValue = switchValue.getConstant();
                        boolean hit = false;
                        // test each case whether hit the target const value
                        for (int i = 0; i < ((SwitchStmt) curStmt).getCaseValues().size(); i++) {
                            int caseValue = ((SwitchStmt) curStmt).getCaseValues().get(i);
                            if (caseValue == realValue) {
                                hit = true;
                                Pair<Integer, Stmt> caseTarget = ((SwitchStmt) curStmt).getCaseTargets().get(i);
                                stmtList.add(caseTarget.second());
                            }
                        }
                        if (!hit) {
                            stmtList.add(((SwitchStmt) curStmt).getDefaultTarget());
                        }
                    } else {
                        for (int i = 0; i < ((SwitchStmt) curStmt).getCaseValues().size(); i++) {
                            Pair<Integer, Stmt> caseTarget = ((SwitchStmt) curStmt).getCaseTargets().get(i);
                            stmtList.add(caseTarget.second());
                        }
                    }
                }
            }
        }

        for(Stmt tmpStmt: cfg.getNodes()) {
            if (tmpStmt == cfg.getEntry() || tmpStmt == cfg.getExit()) {
                continue;
            }
            if (!reachableCode.contains(tmpStmt)) {
                deadCode.add(tmpStmt);
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
