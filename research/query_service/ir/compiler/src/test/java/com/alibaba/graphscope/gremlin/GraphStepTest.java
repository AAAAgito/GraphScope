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

import com.alibaba.graphscope.common.intermediate.operator.ScanFusionOp;
import com.alibaba.graphscope.common.jna.type.FfiConst;
import com.alibaba.graphscope.common.jna.type.FfiNameOrId;
import com.alibaba.graphscope.common.jna.type.FfiScanOpt;
import org.apache.tinkerpop.gremlin.process.traversal.Step;
import org.apache.tinkerpop.gremlin.process.traversal.Traversal;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversalSource;
import org.apache.tinkerpop.gremlin.structure.Graph;
import org.apache.tinkerpop.gremlin.tinkergraph.structure.TinkerFactory;
import org.junit.Assert;
import org.junit.Test;

import java.util.List;

public class GraphStepTest {
    private Graph graph = TinkerFactory.createModern();
    private GraphTraversalSource g = graph.traversal();

    @Test
    public void g_V_test() {
        Traversal traversal = g.V();
        Step graphStep = traversal.asAdmin().getStartStep();
        ScanFusionOp op = (ScanFusionOp) IrPlanBuidler.StepTransformFactory.GRAPH_STEP.apply(graphStep);
        Assert.assertEquals(FfiScanOpt.Vertex, op.getScanOpt().get().getArg());
    }

    @Test
    public void g_E_test() {
        Traversal traversal = g.E();
        Step graphStep = traversal.asAdmin().getStartStep();
        ScanFusionOp op = (ScanFusionOp) IrPlanBuidler.StepTransformFactory.GRAPH_STEP.apply(graphStep);
        Assert.assertEquals(FfiScanOpt.Edge, op.getScanOpt().get().getArg());
    }

    @Test
    public void g_V_label_test() {
        Traversal traversal = g.V().hasLabel("person");
        traversal.asAdmin().applyStrategies();
        Step graphStep = traversal.asAdmin().getStartStep();
        ScanFusionOp op = (ScanFusionOp) IrPlanBuidler.StepTransformFactory.TINKER_GRAPH_STEP.apply(graphStep);
        FfiNameOrId.ByValue ffiLabel = ((List<FfiNameOrId.ByValue>) op.getLabels().get().getArg()).get(0);
        Assert.assertEquals("person", ffiLabel.name);
    }

    @Test
    public void g_V_id_test() {
        Traversal traversal = g.V(1L);
        Step graphStep = traversal.asAdmin().getStartStep();
        ScanFusionOp op = (ScanFusionOp) IrPlanBuidler.StepTransformFactory.GRAPH_STEP.apply(graphStep);
        FfiConst.ByValue ffiId = ((List<FfiConst.ByValue>) op.getIds().get().getArg()).get(0);
        Assert.assertEquals(1L, ffiId.int64);
    }

    @Test
    public void g_V_property_test() {
        Traversal traversal = g.V().has("name", "marko");
        traversal.asAdmin().applyStrategies();
        Step graphStep = traversal.asAdmin().getStartStep();
        ScanFusionOp op = (ScanFusionOp) IrPlanBuidler.StepTransformFactory.TINKER_GRAPH_STEP.apply(graphStep);
        String expr = (String) op.getPredicate().get().getArg();
        Assert.assertEquals("@.name == \"marko\"", expr);
    }
}