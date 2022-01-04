package com.alibaba.graphscope.gremlin.result;

import com.alibaba.graphscope.gremlin.Utils;
import com.alibaba.graphscope.gremlin.exception.UnsupportedStepException;
import org.apache.tinkerpop.gremlin.process.traversal.Step;
import org.apache.tinkerpop.gremlin.process.traversal.Traversal;
import org.apache.tinkerpop.gremlin.process.traversal.step.filter.DedupGlobalStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.filter.HasStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.filter.RangeGlobalStep;
import org.apache.tinkerpop.gremlin.process.traversal.step.map.*;
import org.apache.tinkerpop.gremlin.tinkergraph.process.traversal.step.sideEffect.TinkerGraphStep;

import java.util.List;

public class GremlinResultAnalyzer {
    public static GremlinResultParser analyze(Traversal traversal) {
        List<Step> steps = traversal.asAdmin().getSteps();
        GremlinResultParser parserType = GremlinResultParserFactory.GRAPH_ELEMENT;
        for (Step step : steps) {
            if (Utils.equalClass(step, GraphStep.class)
                    || Utils.equalClass(step, TinkerGraphStep.class) || Utils.equalClass(step, VertexStep.class)) {
                parserType = GremlinResultParserFactory.GRAPH_ELEMENT;
            } else if (Utils.equalClass(step, CountGlobalStep.class) || Utils.equalClass(step, PropertiesStep.class)) {
                parserType = GremlinResultParserFactory.SINGLE_VALUE;
            } else if (Utils.equalClass(step, SelectOneStep.class) || Utils.equalClass(step, SelectStep.class)) {
                parserType = GremlinResultParserFactory.PROJECT_TAG;
            } else if (Utils.equalClass(step, PropertyMapStep.class)) {
                parserType = GremlinResultParserFactory.VALUE_MAP;
            } else if (Utils.equalClass(step, GroupCountStep.class) || Utils.equalClass(step, GroupStep.class)) {
                parserType = GremlinResultParserFactory.GROUP;
            } else if (Utils.equalClass(step, HasStep.class) || Utils.equalClass(step, DedupGlobalStep.class)
                    || Utils.equalClass(step, RangeGlobalStep.class) || Utils.equalClass(step, OrderGlobalStep.class)) {
                // do nothing;
            } else {
                throw new UnsupportedStepException(step.getClass(), "unimplemented yet");
            }
        }
        return parserType;
    }
}