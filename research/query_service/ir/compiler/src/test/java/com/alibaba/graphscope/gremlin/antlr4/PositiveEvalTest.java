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

package com.alibaba.graphscope.gremlin.antlr4;

import com.alibaba.graphscope.gremlin.plugin.script.AntlrToJavaScriptEngine;
import org.apache.tinkerpop.gremlin.process.traversal.P;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversalSource;
import org.apache.tinkerpop.gremlin.structure.Graph;
import org.apache.tinkerpop.gremlin.tinkergraph.structure.TinkerFactory;
import org.junit.Assert;
import org.junit.Before;

import org.junit.Test;

import javax.script.Bindings;
import javax.script.ScriptContext;
import javax.script.SimpleBindings;
import javax.script.SimpleScriptContext;

public class PositiveEvalTest {
    private Graph graph;
    private GraphTraversalSource g;
    private AntlrToJavaScriptEngine scriptEngine;
    private ScriptContext context;

    @Before
    public void before() {
        graph = TinkerFactory.createModern();
        g = graph.traversal();
        Bindings globalBindings = new SimpleBindings();
        globalBindings.put("g", g);
        context = new SimpleScriptContext();
        context.setBindings(globalBindings, ScriptContext.ENGINE_SCOPE);
        scriptEngine = new AntlrToJavaScriptEngine();
    }

    private Object eval(String query) {
        return scriptEngine.eval(query, context);
    }

    @Test
    public void eval_g_V_test() {
        Assert.assertEquals(g.V(), eval("g.V()"));
    }

    @Test
    public void eval_g_E_test() {
        Assert.assertEquals(g.E(), eval("g.E()"));
    }

    // expand
    @Test
    public void eval_g_V_out_test() {
        Assert.assertEquals(g.V().out(), eval("g.V().out()"));
    }

    @Test
    public void eval_g_V_outE_test() {
        Assert.assertEquals(g.V().outE(), eval("g.V().outE()"));
    }

    @Test
    public void eval_g_V_in_test() {
        Assert.assertEquals(g.V().in(), eval("g.V().in()"));
    }

    @Test
    public void eval_g_V_inE_test() {
        Assert.assertEquals(g.V().inE(), eval("g.V().inE()"));
    }

    @Test
    public void eval_g_V_both_test() {
        Assert.assertEquals(g.V().both(), eval("g.V().both()"));
    }

    @Test
    public void eval_g_V_bothE_test() {
        Assert.assertEquals(g.V().bothE(), eval("g.V().bothE()"));
    }

    @Test
    public void eval_g_V_outE_label_test() {
        Assert.assertEquals(g.V().outE("knows"), eval("g.V().outE('knows')"));
    }

    @Test
    public void eval_g_V_out_labels_test() {
        Assert.assertEquals(g.V().out("knows", "has"), eval("g.V().out('knows', 'has')"));
    }

    @Test
    public void eval_g_V_outE_labels_test() {
        Assert.assertEquals(g.V().outE("knows", "has"), eval("g.V().outE('knows', 'has')"));
    }

    @Test
    public void eval_g_V_in_labels_test() {
        Assert.assertEquals(g.V().in("knows", "has"), eval("g.V().in('knows', 'has')"));
    }

    @Test
    public void eval_g_V_inE_labels_test() {
        Assert.assertEquals(g.V().inE("knows", "has"), eval("g.V().inE('knows', 'has')"));
    }

    @Test
    public void eval_g_V_both_labels_test() {
        Assert.assertEquals(g.V().both("knows", "has"), eval("g.V().both('knows', 'has')"));
    }

    @Test
    public void eval_g_V_bothE_labels_test() {
        Assert.assertEquals(g.V().bothE("knows", "has"), eval("g.V().bothE('knows', 'has')"));
    }

    @Test
    public void eval_g_V_outE_label_inV_test() {
        Assert.assertEquals(g.V().outE("knows").inV(), eval("g.V().outE('knows').inV()"));
    }

    @Test
    public void eval_g_V_inE_label_outV_test() {
        Assert.assertEquals(g.V().inE("knows").outV(), eval("g.V().inE('knows').outV()"));
    }

    @Test
    public void eval_g_V_bothE_label_otherV_test() {
        Assert.assertEquals(g.V().bothE("knows").otherV(), eval("g.V().bothE('knows').otherV()"));
    }

    // has

    @Test
    public void g_V_hasLabel() {
        Assert.assertEquals(g.V().hasLabel("person"), eval("g.V().hasLabel('person')"));
    }

    @Test
    public void g_V_hasLabels() {
        Assert.assertEquals(g.V().hasLabel("person", "software"), eval("g.V().hasLabel('person', 'software')"));
    }

    @Test
    public void g_V_hasId() {
        Assert.assertEquals(g.V().hasId(1), eval("g.V().hasId(1)"));
    }

    @Test
    public void g_V_hasIds() {
        Assert.assertEquals(g.V().hasId(1, 2), eval("g.V().hasId(1, 2)"));
    }

    @Test
    public void g_V_has_name_str() {
        Assert.assertEquals(g.V().has("name", "marko"), eval("g.V().has('name', 'marko')"));
    }

    @Test
    public void g_V_has_age_int() {
        Assert.assertEquals(g.V().has("age", 10), eval("g.V().has('age', 10)"));
    }

    // predicate

    @Test
    public void g_V_has_age_P_eq() {
        Assert.assertEquals(g.V().has("age", P.eq(10)), eval("g.V().has('age', eq(10))"));
    }

    @Test
    public void g_V_has_age_P_neq() {
        Assert.assertEquals(g.V().has("age", P.neq(10)), eval("g.V().has('age', neq(10))"));
    }

    @Test
    public void g_V_has_age_P_lt() {
        Assert.assertEquals(g.V().has("age", P.lt(10)), eval("g.V().has('age', lt(10))"));
    }

    @Test
    public void g_V_has_age_P_lte() {
        Assert.assertEquals(g.V().has("age", P.lte(10)), eval("g.V().has('age', lte(10))"));
    }

    @Test
    public void g_V_has_age_P_gt() {
        Assert.assertEquals(g.V().has("age", P.gt(10)), eval("g.V().has('age', gt(10))"));
    }

    @Test
    public void g_V_has_age_P_gte() {
        Assert.assertEquals(g.V().has("age", P.gte(10)), eval("g.V().has('age', gte(10))"));
    }

    // limit

    @Test
    public void g_V_limit() {
        Assert.assertEquals(g.V().limit(1), eval("g.V().limit(1)"));
    }

    @Test
    public void g_V_hasLabel_limit() {
        Assert.assertEquals(g.V().limit(1), eval("g.V().limit(1)"));
    }

    @Test
    public void g_V_limit_hasLabel() {
        Assert.assertEquals(g.V().hasLabel("person").limit(1), eval("g.V().hasLabel('person').limit(1)"));
    }

    @Test
    public void g_V_out_limit() {
        Assert.assertEquals(g.V().out().limit(1), eval("g.V().out().limit(1)"));
    }

    @Test
    public void g_V_hasLabel_out_limit() {
        Assert.assertEquals(g.V().hasLabel("person").out().limit(1), eval("g.V().hasLabel('person').out().limit(1)"));
    }

    @Test
    public void g_V_limit_out_out_limit() {
        Assert.assertEquals(g.V().limit(1).out().out().limit(1), eval("g.V().limit(1).out().out().limit(1)"));
    }

    @Test
    public void g_V_has_property_test() {
        Assert.assertEquals(g.V().has("name", "marko"), eval("g.V().has('name', 'marko')"));
    }

    @Test
    public void g_V_has_eq_test() {
        Assert.assertEquals(g.V().has("name", P.eq("marko")), eval("g.V().has('name', eq('marko'))"));
    }

    @Test
    public void g_V_has_neq_test() {
        Assert.assertEquals(g.V().has("name", P.neq("marko")), eval("g.V().has('name', neq('marko'))"));
    }

    @Test
    public void g_V_has_lt_test() {
        Assert.assertEquals(g.V().has("age", P.lt(10)), eval("g.V().has('age', lt(10))"));
    }

    @Test
    public void g_V_has_lte_test() {
        Assert.assertEquals(g.V().has("age", P.lte(10)), eval("g.V().has('age', lte(10))"));
    }

    @Test
    public void g_V_has_gt_test() {
        Assert.assertEquals(g.V().has("age", P.gt(10)), eval("g.V().has('age', gt(10))"));
    }

    @Test
    public void g_V_has_gte_test() {
        Assert.assertEquals(g.V().has("age", P.gte(10)), eval("g.V().has('age', gte(10))"));
    }

    @Test
    public void g_V_has_within_int_test() {
        Assert.assertEquals(g.V().has("age", P.within(10)), eval("g.V().has('age', within(10))"));
    }

    @Test
    public void g_V_has_within_ints_test() {
        Assert.assertEquals(g.V().has("age", P.within(10, 11)), eval("g.V().has('age', within(10, 11))"));
    }

    @Test
    public void g_V_has_without_int_test() {
        Assert.assertEquals(g.V().has("age", P.without(10)), eval("g.V().has('age', without(10))"));
    }

    @Test
    public void g_V_has_without_ints_test() {
        Assert.assertEquals(g.V().has("age", P.without(10, 11)), eval("g.V().has('age', without(10, 11))"));
    }

    @Test
    public void g_V_has_within_strs_test() {
        Assert.assertEquals(g.V().has("name", P.within("marko", "josh")), eval("g.V().has('name', within('marko', 'josh'))"));
    }

    @Test
    public void g_V_has_without_strs_test() {
        Assert.assertEquals(g.V().has("name", P.without("marko", "josh")), eval("g.V().has('name', without('marko', 'josh'))"));
    }
}