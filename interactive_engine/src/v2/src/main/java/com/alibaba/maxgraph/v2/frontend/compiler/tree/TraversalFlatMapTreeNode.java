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
package com.alibaba.maxgraph.v2.frontend.compiler.tree;

import com.alibaba.maxgraph.proto.v2.OperatorType;
import com.alibaba.maxgraph.proto.v2.RequirementType;
import com.alibaba.maxgraph.proto.v2.RequirementValue;
import com.alibaba.maxgraph.v2.common.frontend.api.schema.GraphSchema;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.LogicalBinaryVertex;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.LogicalQueryPlan;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.LogicalSubQueryPlan;
import com.alibaba.maxgraph.v2.frontend.compiler.logical.LogicalVertex;
import com.alibaba.maxgraph.v2.frontend.compiler.optimizer.ContextManager;
import com.alibaba.maxgraph.v2.frontend.compiler.tree.value.ValueType;
import com.alibaba.maxgraph.v2.frontend.compiler.utils.TreeNodeUtils;

import java.util.List;

public class TraversalFlatMapTreeNode extends UnaryTreeNode {
    private TreeNode flatMapNode;

    public TraversalFlatMapTreeNode(TreeNode input,
                                    GraphSchema schema,
                                    TreeNode flatMapNode) {
        super(input, NodeType.FLATMAP, schema);
        this.flatMapNode = flatMapNode;
        this.validFlatMapNode();
    }

    private void validFlatMapNode() {
        List<TreeNode> nodeList = TreeNodeUtils.buildTreeNodeListFromLeaf(this.flatMapNode);
        for (TreeNode treeNode : nodeList) {
            if (treeNode instanceof GroupTreeNode ||
                    treeNode instanceof GroupCountTreeNode) {
                throw new IllegalArgumentException("Not support group/groupCount in flatMap yet.");
            }
        }
    }

    @Override
    public LogicalSubQueryPlan buildLogicalQueryPlan(ContextManager contextManager) {
        TreeNodeLabelManager treeNodeLabelManager = contextManager.getTreeNodeLabelManager();
        LogicalVertex inputVertex = getInputNode().getOutputVertex();
        LogicalSubQueryPlan logicalQueryPlan = new LogicalSubQueryPlan(contextManager);
        logicalQueryPlan.addLogicalVertex(inputVertex);

        LogicalQueryPlan flatMapPlan = TreeNodeUtils.buildSubQueryPlan(flatMapNode, inputVertex, contextManager);
        logicalQueryPlan.mergeLogicalQueryPlan(flatMapPlan);
        LogicalVertex flatOutputVertex = logicalQueryPlan.getOutputVertex();

        LogicalVertex inputTargetVertex = flatMapPlan.getTargetVertex(inputVertex);
        if (inputTargetVertex.getProcessorFunction().getOperatorType() == OperatorType.ENTER_KEY
                && !(flatOutputVertex instanceof LogicalBinaryVertex)) {
            flatOutputVertex.getAfterRequirementList().add(
                    RequirementValue.newBuilder()
                            .setReqType(RequirementType.KEY_DEL));
        }

        addUsedLabelAndRequirement(flatOutputVertex, treeNodeLabelManager);
        setFinishVertex(flatOutputVertex, treeNodeLabelManager);

        return logicalQueryPlan;
    }

    @Override
    public void addPathRequirement() {
        List<TreeNode> nodeList = TreeNodeUtils.buildTreeNodeListFromLeaf(flatMapNode);
        for (int i = 1; i < nodeList.size(); i++) {
            TreeNode node = nodeList.get(i);
            if (node.getNodeType() != NodeType.FILTER) {
                node.addPathRequirement();
                break;
            }
        }
    }

    @Override
    public ValueType getOutputValueType() {
        return flatMapNode.getOutputValueType();
    }
}
