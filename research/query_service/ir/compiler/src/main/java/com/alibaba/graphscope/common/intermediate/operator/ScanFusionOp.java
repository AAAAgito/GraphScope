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

package com.alibaba.graphscope.common.intermediate.operator;

import java.util.Optional;

public class ScanFusionOp extends InterOpBase {
    public ScanFusionOp() {
        super();
        scanOpt = Optional.empty();
        labels = Optional.empty();
        properties = Optional.empty();
        ids = Optional.empty();
        predicate = Optional.empty();
        limit = Optional.empty();
    }

    // vertex or edge
    private Optional<OpArg> scanOpt;

    // scan by labels
    private Optional<OpArg> labels;

    // scan by properties
    private Optional<OpArg> properties;

    // indexing based on id
    private Optional<OpArg> ids;

    // filter by predicate
    private Optional<OpArg> predicate;

    // filter by limit
    private Optional<OpArg> limit;

    public Optional<OpArg> getScanOpt() {
        return scanOpt;
    }

    public Optional<OpArg> getLabels() {
        return labels;
    }

    public Optional<OpArg> getProperties() {
        return properties;
    }

    public Optional<OpArg> getIds() {
        return ids;
    }

    public Optional<OpArg> getPredicate() {
        return predicate;
    }

    public Optional<OpArg> getLimit() {
        return limit;
    }

    public void setScanOpt(OpArg scanOpt) {
        this.scanOpt = Optional.of(scanOpt);
    }

    public void setLabels(OpArg labels) {
        this.labels = Optional.of(labels);
    }

    public void setProperties(OpArg properties) {
        this.properties = Optional.of(properties);
    }

    public void setIds(OpArg ids) {
        this.ids = Optional.of(ids);
    }

    public void setPredicate(OpArg predicate) {
        this.predicate = Optional.of(predicate);
    }

    public void setLimit(OpArg limit) {
        this.limit = Optional.of(limit);
    }
}
