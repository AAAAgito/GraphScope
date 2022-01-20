/*
 * Copyright 2020 Alibaba Group Holding Limited.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.alibaba.graphscope.gremlin;

import com.alibaba.graphscope.common.exception.OpArgIllegalException;
import org.apache.tinkerpop.gremlin.process.traversal.P;
import org.apache.tinkerpop.gremlin.process.traversal.Traversal;
import org.apache.tinkerpop.gremlin.process.traversal.lambda.IdentityTraversal;
import org.apache.tinkerpop.gremlin.process.traversal.lambda.ValueTraversal;
import org.apache.tinkerpop.gremlin.process.traversal.step.filter.IsStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.filter.WherePredicateStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.map.PropertiesStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.util.HasContainer;
import org.apache.tinkerpop.gremlin.process.traversal.util.ConnectiveP;
import org.apache.tinkerpop.gremlin.process.traversal.util.TraversalRing;

import java.util.Iterator;
import java.util.List;
import java.util.Optional;

public enum PredicateExprTransformFactory implements PredicateExprTransform {
    EXPR_FROM_CONTAINERS {
        @Override
        public String apply(Object arg) {
            List<HasContainer> containers = (List<HasContainer>) arg;
            String expr = "";
            for (int i = 0; i < containers.size(); ++i) {
                if (i > 0) {
                    expr += " && ";
                }
                HasContainer container = containers.get(i);
                String key = "@." + container.getKey();
                expr += flatPredicate(key, container.getPredicate());
            }
            return expr;
        }
    },
    EXPR_FROM_IS_STEP {
        @Override
        public String apply(Object arg) {
            IsStep isStep = (IsStep) arg;
            // current value
            String key = "@";
            return flatPredicate(key, isStep.getPredicate());
        }
    },
    EXPR_FROM_WHERE_PREDICATE {
        @Override
        public String apply(Object arg) {
            WherePredicateStep step = (WherePredicateStep) arg;
            Optional<String> startKey = step.getStartKey();
            TraversalRing traversalRing = Utils.getFieldValue(WherePredicateStep.class, step, "traversalRing");

            String startTag = startKey.isPresent() ? startKey.get() : "";
            String startBy = getTagByTraversal(startTag, traversalRing.next());

            P predicate = (P) step.getPredicate().get();
            List<String> selectKeys = Utils.getFieldValue(WherePredicateStep.class, step, "selectKeys");
            traverseAndUpdateP(predicate, selectKeys.iterator(), traversalRing);

            return flatPredicate(startBy, predicate);
        }

        private void traverseAndUpdateP(P predicate, Iterator<String> selectKeysIterator, TraversalRing traversalRing) {
            if (predicate instanceof ConnectiveP) {
                ((ConnectiveP) predicate).getPredicates().forEach(p1 -> {
                    traverseAndUpdateP((P) p1, selectKeysIterator, traversalRing);
                });
            } else {
                String tagProperty = getTagByTraversal(selectKeysIterator.next(), traversalRing.next());
                predicate.setValue(new WherePredicateValue(tagProperty));
            }
        }

        private String getTagByTraversal(String tag, Traversal.Admin byTraversal) {
            String expr;
            if (byTraversal == null || byTraversal instanceof IdentityTraversal) {
                expr = "@" + tag;
            } else if (byTraversal instanceof ValueTraversal) {
                String property = ((ValueTraversal) byTraversal).getPropertyKey();
                expr = String.format("@%s.%s", tag, property);
            } else if (byTraversal.getSteps().size() == 1 && byTraversal.getStartStep() instanceof PropertiesStep) {
                String[] mapKeys = ((PropertiesStep) byTraversal.getStartStep()).getPropertyKeys();
                if (mapKeys.length == 0) {
                    throw new OpArgIllegalException(OpArgIllegalException.Cause.UNSUPPORTED_TYPE, "values() is unsupported");
                }
                if (mapKeys.length > 1) {
                    throw new OpArgIllegalException(OpArgIllegalException.Cause.UNSUPPORTED_TYPE,
                            "use valueMap(..) instead if there are multiple project keys");
                }
                expr = String.format("@%s.%s", tag, mapKeys[0]);
            } else {
                throw new OpArgIllegalException(OpArgIllegalException.Cause.UNSUPPORTED_TYPE,
                        "supported pattern is [by()] or [by('name')] or [by(values('name'))]");
            }
            // todo: by(valueMap)
            return expr;
        }
    };

    public class WherePredicateValue {
        private String predicateValue;

        public WherePredicateValue(String predicateValue) {
            this.predicateValue = predicateValue;
        }

        @Override
        public String toString() {
            return predicateValue;
        }
    }
}
