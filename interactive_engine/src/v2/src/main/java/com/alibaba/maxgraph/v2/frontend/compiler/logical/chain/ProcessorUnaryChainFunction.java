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
package com.alibaba.maxgraph.v2.frontend.compiler.logical.chain;


import com.alibaba.maxgraph.proto.v2.OperatorType;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.LogicalVertex;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.function.ProcessorFunction;

import java.util.List;

public class ProcessorUnaryChainFunction extends ProcessorFunction implements ProcessorChainFunction {
    private List<LogicalVertex> chainVertexList;

    public ProcessorUnaryChainFunction(List<LogicalVertex> chainVertexList) {
        super(OperatorType.UNARY_CHAIN);
        this.chainVertexList = chainVertexList;
    }

    @Override
    public List<LogicalVertex> getChainVertexList() {
        return this.chainVertexList;
    }
}
