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
package com.alibaba.maxgraph.compiler.tree.value;

import com.alibaba.maxgraph.Message;
import com.google.common.base.MoreObjects;

@Deprecated
public class ElementValueType implements ValueType {
    private final ElementType elementType;
    private final Message.VariantType variantType;

    public ElementValueType(ElementType elementType, Message.VariantType variantType) {
        this.elementType = elementType;
        this.variantType = variantType;
    }

    public ElementType getElementType() {
        return elementType;
    }

    public Message.VariantType getVariantType() {
        return variantType;
    }

    @Override
    public int hashCode() {
        return this.getClass().getName().hashCode();
    }

    @Override
    public boolean equals(Object that) {
        if (null == that || getClass() != that.getClass()) {
            return false;
        }

        return true;
    }

    @Override
    public String toString() {
        return MoreObjects.toStringHelper(this).toString();
    }
}
