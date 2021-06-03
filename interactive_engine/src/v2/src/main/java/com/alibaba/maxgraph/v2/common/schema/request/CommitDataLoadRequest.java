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
package com.alibaba.maxgraph.v2.common.schema.request;

import com.alibaba.maxgraph.proto.v2.PrepareDataLoadPb;
import com.alibaba.maxgraph.v2.common.operation.OperationType;
import com.alibaba.maxgraph.v2.sdk.DataLoadTarget;
import com.google.protobuf.ByteString;

public class CommitDataLoadRequest extends AbstractDdlRequest {

    private DataLoadTarget dataLoadTarget;
    private long tableId;

    public CommitDataLoadRequest(DataLoadTarget dataLoadTarget, long tableId) {
        super(OperationType.COMMIT_DATA_LOAD);
        this.dataLoadTarget = dataLoadTarget;
        this.tableId = tableId;
    }

    @Override
    protected ByteString getBytes() {
        return PrepareDataLoadPb.newBuilder()
                .setTarget(dataLoadTarget.toProto())
                .setTableIdx(this.tableId)
                .build().toByteString();
    }
}
