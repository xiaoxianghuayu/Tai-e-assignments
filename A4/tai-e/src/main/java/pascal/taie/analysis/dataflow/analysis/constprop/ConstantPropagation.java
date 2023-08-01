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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundaryFact = new CPFact();
        for(Var param: cfg.getIR().getParams()) {   // cfg.getIR return `DefaultIR` of <SimpleBinary: int nac(int)>, i.e. the whole function information
            if(canHoldInt(param)) {
                boundaryFact.update(param, Value.getNAC());
            }
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var key: fact.keySet()) {
            Value value = meetValue(fact.get(key), target.get(key));
            target.update(key, value);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value value = null;
        if(v1.isNAC() || v2.isNAC()) {
            value = Value.getNAC();
        } else if(v1.isUndef()) {
            value = v2;
        } else if(v2.isUndef()) {
            value = v1;
        } else if(v1.isConstant() && v2.isConstant()) {
            if(v1.getConstant() == v2.getConstant()) {
                value = Value.makeConstant(v1.getConstant());
            } else {
                value = Value.getNAC();
            }
        }

        return value;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = false;
        CPFact newOut = in.copy();

        if(stmt.getUses().size() == 0) {
            // control instruction, ignore
        } else {
            if(!stmt.getDef().isEmpty() && stmt.getDef().get() instanceof Var) {
                Exp rightExp = stmt.getUses().get(stmt.getUses().size() - 1);
                Value rightValue = evaluate(rightExp, in);

                Var leftValue = (Var)stmt.getDef().get();

                if(canHoldInt(leftValue)) {                 // the var can not hold int will always be the init value: Value.getNAC()
                    newOut.update(leftValue, rightValue);   // update includes add and remove
                }
            }
            // function declaration, return, control instruction(if)
        }

        if(!newOut.equals(out)) {
            changed = true;
        }
        out.clear();
        out.copyFrom(newOut);

        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        Value value = null;

        if (exp instanceof Var) {
            Var tVar = ((Var) exp);
            value = in.get(tVar);
        } else if (exp instanceof IntLiteral) {
            value = Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            Var op1 = ((BinaryExp) exp).getOperand1();
            Var op2 = ((BinaryExp) exp).getOperand2();
            Value value1 = in.get(op1);
            Value value2 = in.get(op2);

            if (value1.isConstant() && value2.isConstant()) {
                int t1 = value1.getConstant();
                int t2 = value2.getConstant();
                int tResult = 0xdeadbeef;
                switch (op.toString()) {
                    case "==" -> tResult = t1 == t2 ? 1 : 0;
                    case "!=" -> tResult = t1 != t2 ? 1 : 0;
                    case "<" -> tResult = t1 < t2 ? 1 : 0;
                    case ">" -> tResult = t1 > t2 ? 1 : 0;
                    case "<=" -> tResult = t1 <= t2 ? 1 : 0;
                    case ">=" -> tResult = t1 >= t2 ? 1 : 0;

                    case "|" -> tResult = t1 | t2;
                    case "&" -> tResult = t1 & t2;
                    case "^" -> tResult = t1 ^ t2;

                    case ">>" -> tResult = t1 >> t2;
                    case "<<" -> tResult = t1 << t2;
                    case ">>>" -> tResult = t1 >>> t2;

                    case "+" -> tResult = t1 + t2;
                    case "-" -> tResult = t1 - t2;
                    case "*" -> tResult = t1 * t2;
                    case "/" -> {
                        if (t2 == 0) {
                            value = Value.getUndef();
                        } else {
                            tResult = t1 / t2;
                        }
                    }
                    case "%" -> {
                        if (t2 == 0) {
                            value = Value.getUndef();
                        } else {
                            tResult = t1 % t2;
                        }
                    }
                    default -> throw new AnalysisException(exp.toString() + " is not supported");
                }
                if (value == null) {
                    value = Value.makeConstant(tResult);
                }
            } else if (value1.isNAC() || value2.isNAC()) {
                value = Value.getNAC();
                if (value1.isNAC() && !value2.isNAC() && value2.getConstant() == 0 && (op.toString() == "/" || op.toString() == "%")) {
                    value = Value.getUndef();
                }
            } else {
                value = Value.getUndef();
            }
        } else {
            value = Value.getNAC();
        }

        return value;
    }
}
