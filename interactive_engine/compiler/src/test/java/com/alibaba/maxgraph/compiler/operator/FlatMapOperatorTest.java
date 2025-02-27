/**
 * Copyright 2020 Alibaba Group Holding Limited.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.alibaba.maxgraph.compiler.operator;

import static org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.__.out;

import org.junit.Test;

import java.io.IOException;

public class FlatMapOperatorTest extends AbstractOperatorTest {
    public FlatMapOperatorTest() throws IOException {}

    @Test
    public void testFlatMapOut() {
        executeTreeQuery(g.V().flatMap(out()).both());
    }

    @Test
    public void testFlatMapOutFold() {
        executeTreeQuery(g.V().flatMap(out().fold()).count());
    }

    @Test
    public void testFlatMap2OutCount() {
        executeTreeQuery(g.V().flatMap(out().out().count()).count());
    }

    @Test
    public void testFlatMapOrderLimit() {
        executeTreeQuery(
                g.V().hasLabel("person")
                        .flatMap(out().order().by("firstName").limit(10))
                        .both()
                        .path());
    }

    @Test
    public void testFlatMap2OutPath() {
        executeTreeQuery(g.V().hasLabel("person").flatMap(out().out()).both().path());
    }

    //    @Test
    //    public void testFlatMapGroupCount() {
    //        executeTreeQuery(g.V().flatMap(out().out().groupCount()).path());
    //    }
}
