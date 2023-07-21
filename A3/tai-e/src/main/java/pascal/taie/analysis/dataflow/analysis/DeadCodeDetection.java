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

        boolean unreachable = false;
        for (Stmt stm: cfg.getNodes()) {
            if (cfg.isEntry(stm) || cfg.isExit(stm)) {
                continue;
            }
            // Add unreachable code
            if (unreachable) {
                deadCode.add(stm);
                continue;
            }

            // handle unreachable branch
            if (stm instanceof If) {
                ConditionExp conditionExp = ((If) stm).getCondition();
                Value conditionExpResult = ConstantPropagation.evaluate(conditionExp, constants.getInFact(stm));
                // if the condition is fixed
                if (conditionExpResult.isConstant()) {
                    Edge<Stmt> trueEdge = null;
                    Edge<Stmt> falseEdge = null;
                    for (Edge <Stmt> tmpStmt: cfg.getOutEdgesOf(stm)) {
                        if (tmpStmt.getKind() == Edge.Kind.IF_TRUE) {
                            trueEdge = tmpStmt;
                        } else if (tmpStmt.getKind() == Edge.Kind.IF_FALSE) {
                            falseEdge = tmpStmt;
                        }
                    }

                    int realValue = conditionExpResult.getConstant();
                    Stmt firstTarget = realValue > 0 ? falseEdge.getTarget() : trueEdge.getTarget();
                    Stmt auxiliaryTarget = realValue > 0 ? trueEdge.getTarget() : falseEdge.getTarget();

                    List<Stmt> auxiliaryWorkList = new ArrayList<>();
                    auxiliaryWorkList.add(auxiliaryTarget);
                    int auxliaryCount = 0;
                    while(auxliaryCount < auxiliaryWorkList.size()) {
                        Stmt currentStmt = auxiliaryWorkList.get(auxliaryCount);
                        auxliaryCount += 1;

                        for (Edge<Stmt> nextEdge : cfg.getOutEdgesOf(currentStmt)) {
                            if (nextEdge.getKind() == Edge.Kind.ENTRY || nextEdge.getKind() == Edge.Kind.RETURN) {
                                continue;
                            }
                            Stmt nextStmt = nextEdge.getTarget();

                            if (!auxiliaryWorkList.contains(nextStmt)) {
                                auxiliaryWorkList.add(nextStmt);
                            }
                        }
                    }

                    List<Stmt> workList = new ArrayList<>();
                    workList.add(firstTarget);
                    deadCode.add(firstTarget);
                    while(workList.size() > 0) {
                        Stmt currentStmt = workList.get(0);
                        workList.remove(currentStmt);
                        if (!auxiliaryWorkList.contains(currentStmt)) {
                            deadCode.add(currentStmt);
                        }
                        for (Edge<Stmt> nextEdge: cfg.getOutEdgesOf(currentStmt)) {
                            if (nextEdge.getKind() == Edge.Kind.ENTRY || nextEdge.getKind() == Edge.Kind.RETURN) {
                                continue;
                            }
                            if (nextEdge.getKind() == Edge.Kind.GOTO) {
                                break;
                            }
                            Stmt nextStmt = nextEdge.getTarget();

                            workList.add(nextStmt);
                        }
                    }
                }
            } else if (stm instanceof SwitchStmt) {
                Var switchVar = ((SwitchStmt) stm).getVar();
                Value switchValue = constants.getInFact(stm).get(switchVar);
                if (switchValue.isConstant()) {
                    int realValue = switchValue.getConstant();
                    boolean hit = false;
                    // test each case whether hit the target const value, if not, delete it
                    for(int i = 0; i < ((SwitchStmt) stm).getCaseValues().size(); i++) {
                        int caseValue = ((SwitchStmt) stm).getCaseValues().get(i);
                        if (caseValue != realValue) {
                            Pair<Integer, Stmt> caseTarget = ((SwitchStmt) stm).getCaseTargets().get(i);

                            Stmt firstTarget = caseTarget.second();
                            List<Stmt> workList = new ArrayList<>();
                            workList.add(firstTarget);
                            deadCode.add(firstTarget);
                            while(workList.size() > 0) {
                                Stmt currentStmt = workList.get(0);
                                workList.remove(currentStmt);
                                deadCode.add(currentStmt);
                                for (Edge<Stmt> nextEdge: cfg.getOutEdgesOf(currentStmt)) {
                                    if (nextEdge.getKind() == Edge.Kind.ENTRY || nextEdge.getKind() == Edge.Kind.RETURN) {
                                        continue;
                                    }
                                    if (nextEdge.getKind() == Edge.Kind.GOTO) {
                                        break;
                                    }
                                    Stmt nextStmt = nextEdge.getTarget();
                                    workList.add(nextStmt);
                                }
                            }
                        } else {
                            hit = true;
                        }

                        // if hit, delete the default part. (what if there are no break in case clause.
                        if (hit) {
                            Stmt firstTarget = ((SwitchStmt) stm).getDefaultTarget();
                            List<Stmt> workList = new ArrayList<>();
                            workList.add(firstTarget);
                            deadCode.add(firstTarget);
                            while(workList.size() > 0) {
                                Stmt currentStmt = workList.get(0);
                                workList.remove(currentStmt);
                                deadCode.add(currentStmt);
                                for (Edge<Stmt> nextEdge: cfg.getOutEdgesOf(currentStmt)) {
                                    if (nextEdge.getKind() == Edge.Kind.ENTRY || nextEdge.getKind() == Edge.Kind.RETURN) {
                                        continue;
                                    }
                                    if (nextEdge.getKind() == Edge.Kind.GOTO) {
                                        // just a test
                                        deadCode.add(cfg.getNodes().stream().toList().get(cfg.getNodes().stream().toList().indexOf(currentStmt) + 1));
                                        break;
                                    }
                                    Stmt nextStmt = nextEdge.getTarget();
                                    workList.add(nextStmt);
                                }
                            }
                        }
                    }

                }
                int deadbeef = 0;
            }

            // Add dead variable
            Optional<LValue> left = stm.getDef();
            if(!left.isEmpty()) {
                LValue lValue = left.get();
                if (!liveVars.getOutFact(stm).contains((Var) lValue)) { // not live var
                    RValue rValue = stm.getUses().get(stm.getUses().size() - 1);
                    if (hasNoSideEffect(rValue)) {
                        deadCode.add(stm);
                        continue;
                    }
                }
            }

            if (stm instanceof Return) {
                unreachable = true;
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
