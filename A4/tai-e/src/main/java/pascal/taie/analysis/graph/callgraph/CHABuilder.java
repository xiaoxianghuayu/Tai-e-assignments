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

package pascal.taie.analysis.graph.callgraph;

import org.jf.dexlib2.dexbacked.raw.CallSiteIdItem;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        ArrayList<JMethod> workList = new ArrayList<>();
        workList.add(entry);

        while (workList.size() > 0) {
            JMethod m = workList.get(0);
            workList.remove(m);

            if (!callGraph.reachableMethods.contains(m)) {
                // add current Method m to reachableMethods
                callGraph.addReachableMethod(m);

                // get all call sites in the Method m
                Stream<Invoke> callSites = callGraph.callSitesIn(m);

                callSites.forEach(cs -> {
                    Set<JMethod> T = resolve(cs);
                    for (JMethod target: T) {
                        if (target == null) {
                            continue;
                        }
                        CallKind newKindType = CallKind.SPECIAL;
                        if (target.isStatic()) {
                            newKindType = CallKind.STATIC;
                        }
                        callGraph.addEdge(new Edge<>(newKindType, cs, target));
                        workList.add(target);
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> result = new HashSet<>();
        MethodRef calleeMethodProgInfo = callSite.getMethodRef();

        JClass calleeMethodDeclaredClass = calleeMethodProgInfo.getDeclaringClass();
        Subsignature calleeMethodSubSig = calleeMethodProgInfo.getSubsignature();

        // slides show that result = {calleeMethodSubSig}, but does not it should be a JMethod?
        if (callSite.isStatic()) {
            // just return the method
            result.add(calleeMethodDeclaredClass.getDeclaredMethod(calleeMethodSubSig));
        } else if(callSite.isSpecial()) {
            // the class type of calleeMethodSubSig
            result.add(dispatch(calleeMethodDeclaredClass, calleeMethodSubSig));
        } else if(callSite.isVirtual()) {
            // the declared type of receiver var
            result.add(dispatch(calleeMethodDeclaredClass, calleeMethodSubSig));

            for (JClass subclassOfCallee: hierarchy.getDirectSubclassesOf(calleeMethodDeclaredClass)) {
                result.add(dispatch(subclassOfCallee, calleeMethodSubSig));
            }
        } else if(callSite.isInterface()) {
            result.add(dispatch(calleeMethodDeclaredClass, calleeMethodSubSig));

            for (JClass subinterfaceOfCallee: hierarchy.getDirectImplementorsOf(calleeMethodDeclaredClass)) {
                result.add(dispatch(subinterfaceOfCallee, calleeMethodSubSig));

                // a class that implements a interface can also be extended
                for (JClass subclassOfCallee: hierarchy.getDirectSubclassesOf(subinterfaceOfCallee)) {
                    result.add(dispatch(subclassOfCallee, calleeMethodSubSig));
                }
            }

            // just for test
            for (JClass tmp: hierarchy.getDirectSubinterfacesOf(calleeMethodDeclaredClass)) {
                for (JClass subinterfaceOfCallee: hierarchy.getDirectImplementorsOf(tmp)) {
                    result.add(dispatch(subinterfaceOfCallee, calleeMethodSubSig));

                    // a class that implements a interface can also be extended
                    for (JClass subclassOfCallee: hierarchy.getDirectSubclassesOf(subinterfaceOfCallee)) {
                        result.add(dispatch(subclassOfCallee, calleeMethodSubSig));
                    }
                }
            }
        }

        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        if (jclass != null ) {
            Collection<JMethod> declaredMethods = jclass.getDeclaredMethods();
            for (JMethod declaredMethod: declaredMethods) {
                if (!declaredMethod.isAbstract() && declaredMethod.getSubsignature() == subsignature) {
                    return declaredMethod;
                }
            }
            return dispatch(jclass.getSuperClass(), subsignature);
        }

        return null;
    }
}
