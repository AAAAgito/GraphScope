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

package com.alibaba.graphscope.gremlin.service;

import com.alibaba.graphscope.gremlin.plugin.processor.IrOpLoader;

import io.netty.channel.ChannelHandler;
import io.netty.channel.ChannelHandlerContext;

import org.apache.tinkerpop.gremlin.driver.message.RequestMessage;
import org.apache.tinkerpop.gremlin.driver.message.ResponseMessage;
import org.apache.tinkerpop.gremlin.driver.message.ResponseStatusCode;
import org.apache.tinkerpop.gremlin.groovy.engine.GremlinExecutor;
import org.apache.tinkerpop.gremlin.server.*;
import org.apache.tinkerpop.gremlin.server.handler.OpSelectorHandler;
import org.apache.tinkerpop.gremlin.server.op.OpProcessorException;
import org.javatuples.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;
import java.util.Optional;
import java.util.concurrent.ScheduledExecutorService;

@ChannelHandler.Sharable
public class IrOpSelectorHandler extends OpSelectorHandler {
    private static final Logger logger = LoggerFactory.getLogger(IrOpSelectorHandler.class);

    private final Settings settings;
    private final GraphManager graphManager;
    private final GremlinExecutor gremlinExecutor;
    private final ScheduledExecutorService scheduledExecutorService;

    public IrOpSelectorHandler(
            final Settings settings,
            final GraphManager graphManager,
            final GremlinExecutor gremlinExecutor,
            final ScheduledExecutorService scheduledExecutorService,
            final Channelizer channelizer) {
        super(settings, graphManager, gremlinExecutor, scheduledExecutorService, channelizer);
        this.settings = settings;
        this.graphManager = graphManager;
        this.gremlinExecutor = gremlinExecutor;
        this.scheduledExecutorService = scheduledExecutorService;
    }

    @Override
    protected void decode(ChannelHandlerContext ctx, RequestMessage msg, List<Object> objects) {
        Context gremlinServerContext =
                new Context(
                        msg,
                        ctx,
                        this.settings,
                        this.graphManager,
                        this.gremlinExecutor,
                        this.scheduledExecutorService);
        try {
            Optional<OpProcessor> processor = IrOpLoader.getProcessor(msg.getProcessor());
            if (!processor.isPresent()) {
                String errorMessage =
                        String.format("Invalid OpProcessor requested [%s]", msg.getProcessor());
                throw new OpProcessorException(
                        errorMessage,
                        ResponseMessage.build(msg)
                                .code(ResponseStatusCode.REQUEST_ERROR_INVALID_REQUEST_ARGUMENTS)
                                .statusMessage(errorMessage)
                                .create());
            }

            objects.add(Pair.with(msg, (processor.get()).select(gremlinServerContext)));
        } catch (OpProcessorException var7) {
            logger.error(var7.getMessage(), var7);
            ctx.writeAndFlush(var7.getResponseMessage());
        }
    }
}
