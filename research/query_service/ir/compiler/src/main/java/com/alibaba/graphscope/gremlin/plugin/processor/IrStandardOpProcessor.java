/*
 * This file is referred and derived from project apache/tinkerpop
 *
 * https://github.com/apache/tinkerpop/blob/master/gremlin-server/src/main/java/org/apache/tinkerpop/gremlin/server/op/AbstractEvalOpProcessor.java
 *
 * which has the following license:
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements. See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership. The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

package com.alibaba.graphscope.gremlin.plugin.processor;

import com.alibaba.graphscope.common.IrPlan;
import com.alibaba.graphscope.common.client.*;
import com.alibaba.graphscope.common.config.Configs;
import com.alibaba.graphscope.common.config.PegasusConfig;
import com.alibaba.graphscope.common.intermediate.InterOpCollection;
import com.alibaba.graphscope.gremlin.InterOpCollectionBuilder;
import com.alibaba.graphscope.gremlin.plugin.script.AntlrToJavaScriptEngineFactory;
import com.alibaba.pegasus.service.protocol.PegasusClient;
import com.google.protobuf.InvalidProtocolBufferException;
import org.apache.tinkerpop.gremlin.driver.message.RequestMessage;
import org.apache.tinkerpop.gremlin.driver.message.ResponseMessage;
import org.apache.tinkerpop.gremlin.driver.message.ResponseStatusCode;
import org.apache.tinkerpop.gremlin.groovy.engine.GremlinExecutor;
import org.apache.tinkerpop.gremlin.groovy.jsr223.TimedInterruptTimeoutException;
import org.apache.tinkerpop.gremlin.process.traversal.Traversal;
import org.apache.tinkerpop.gremlin.process.traversal.dsl.graph.GraphTraversalSource;
import org.apache.tinkerpop.gremlin.server.Context;
import org.apache.tinkerpop.gremlin.server.Settings;
import org.apache.tinkerpop.gremlin.server.op.AbstractEvalOpProcessor;
import org.apache.tinkerpop.gremlin.server.op.OpProcessorException;
import org.apache.tinkerpop.gremlin.server.op.standard.StandardOpProcessor;
import org.apache.tinkerpop.gremlin.structure.Graph;
import org.apache.tinkerpop.gremlin.tinkergraph.structure.TinkerFactory;
import org.codehaus.groovy.control.MultipleCompilationErrorsException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.script.Bindings;
import javax.script.SimpleBindings;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.TimeoutException;
import java.util.function.Supplier;

public class IrStandardOpProcessor extends StandardOpProcessor {
    private static Logger logger = LoggerFactory.getLogger(IrStandardOpProcessor.class);
    private Graph graph;
    private GraphTraversalSource g;
    private Configs configs;
    private AbstractBroadcastProcessor broadcastProcessor;

    public IrStandardOpProcessor(Configs configs) {
        this.graph = TinkerFactory.createModern();
        this.g = graph.traversal();
        this.configs = configs;
        RpcChannelFetcher channelFetcher = new HostsChannelFetcher(configs);
        broadcastProcessor = new RpcBroadcastProcessor(channelFetcher);
    }

    @Override
    protected void evalOpInternal(final Context ctx, final Supplier<GremlinExecutor> gremlinExecutorSupplier, final AbstractEvalOpProcessor.BindingSupplier bindingsSupplier) {
        com.codahale.metrics.Timer.Context timerContext = evalOpTimer.time();
        RequestMessage msg = ctx.getRequestMessage();
        GremlinExecutor gremlinExecutor = gremlinExecutorSupplier.get();
        Map<String, Object> args = msg.getArgs();
        String script = (String) args.get("gremlin");
        // replace with antlr parser
        String language = AntlrToJavaScriptEngineFactory.ENGINE_NAME;
        Bindings bindings = new SimpleBindings();

        GremlinExecutor.LifeCycle lifeCycle = createLifeCycle(ctx, gremlinExecutorSupplier, bindingsSupplier);

        try {
            CompletableFuture<Object> evalFuture = gremlinExecutor.eval(script, language, bindings, lifeCycle);
            evalFuture.handle((v, t) -> {
                long elapsed = timerContext.stop();
                logger.info("query \"{}\" total execution time is {} ms", script, elapsed / 1000000.0f);
                if (t != null) {
                    Optional<Throwable> possibleTemporaryException = determineIfTemporaryException(t);
                    if (possibleTemporaryException.isPresent()) {
                        ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.SERVER_ERROR_TEMPORARY).statusMessage(((Throwable) possibleTemporaryException.get()).getMessage()).statusAttributeException((Throwable) possibleTemporaryException.get()).create());
                    } else if (t instanceof OpProcessorException) {
                        ctx.writeAndFlush(((OpProcessorException) t).getResponseMessage());
                    } else {
                        String errorMessage;
                        if (t instanceof TimedInterruptTimeoutException) {
                            errorMessage = String.format("A timeout occurred within the script during evaluation of [%s] - consider increasing the limit given to TimedInterruptCustomizerProvider", msg);
                            logger.warn(errorMessage);
                            ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.SERVER_ERROR_TIMEOUT).statusMessage("Timeout during script evaluation triggered by TimedInterruptCustomizerProvider").statusAttributeException(t).create());
                        } else if (t instanceof TimeoutException) {
                            errorMessage = String.format("Script evaluation exceeded the configured threshold for request [%s]", msg);
                            logger.warn(errorMessage, t);
                            ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.SERVER_ERROR_TIMEOUT).statusMessage(t.getMessage()).statusAttributeException(t).create());
                        } else if (t instanceof MultipleCompilationErrorsException && t.getMessage().contains("Method too large") && ((MultipleCompilationErrorsException) t).getErrorCollector().getErrorCount() == 1) {
                            errorMessage = String.format("The Gremlin statement that was submitted exceeds the maximum compilation size allowed by the JVM, please split it into multiple smaller statements - %s", msg);
                            logger.warn(errorMessage);
                            ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.SERVER_ERROR_EVALUATION).statusMessage(errorMessage).statusAttributeException(t).create());
                        } else {
                            errorMessage = t.getMessage() == null ? t.toString() : t.getMessage();
                            logger.warn(String.format("Exception processing a script on request [%s].", msg), t);
                            ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.SERVER_ERROR_EVALUATION).statusMessage(errorMessage).statusAttributeException(t).create());
                        }
                    }
                }

                return null;
            });
        } catch (RejectedExecutionException var17) {
            ctx.writeAndFlush(ResponseMessage.build(msg).code(ResponseStatusCode.TOO_MANY_REQUESTS).statusMessage("Rate limiting").create());
        }

    }

    protected GremlinExecutor.LifeCycle createLifeCycle(Context ctx, Supplier<GremlinExecutor> gremlinExecutorSupplier, BindingSupplier bindingsSupplier) {
        final RequestMessage msg = ctx.getRequestMessage();
        final Settings settings = ctx.getSettings();
        final Map<String, Object> args = msg.getArgs();
        long seto = args.containsKey("evaluationTimeout") ? ((Number) args.get("evaluationTimeout")).longValue() : settings.getEvaluationTimeout();

        return GremlinExecutor.LifeCycle.build()
                .evaluationTimeoutOverride(seto)
                .beforeEval(b -> {
                    try {
                        b.putAll(bindingsSupplier.get());
                        b.put("graph", graph);
                        b.put("g", g);
                    } catch (OpProcessorException ope) {
                        throw new RuntimeException(ope);
                    }
                })
                .withResult(o -> {
                    try {
                        if (o != null && o instanceof Traversal) {
                            InterOpCollection opCollection = (new InterOpCollectionBuilder((Traversal) o)).build();
                            IrPlan irPlan = opCollection.buildIrPlan();

                            byte[] physicalPlanBytes = irPlan.toPhysicalBytes();
                            irPlan.close();

                            int serverNum = PegasusConfig.PEGASUS_HOSTS.get(configs).split(",").length;
                            List<Long> servers = new ArrayList<>();
                            for (long i = 0; i < serverNum; ++i) {
                                servers.add(i);
                            }

                            PegasusClient.JobRequest request = PegasusClient.JobRequest.parseFrom(physicalPlanBytes);
                            PegasusClient.JobConfig jobConfig = PegasusClient.JobConfig.newBuilder()
                                    .setJobId(1)
                                    .setJobName("ir_plan_1")
                                    .setWorkers(PegasusConfig.PEGASUS_WORKER_NUM.get(configs))
                                    .setBatchSize(PegasusConfig.PEGASUS_BATCH_SIZE.get(configs))
                                    .setMemoryLimit(PegasusConfig.PEGASUS_MEMORY_LIMIT.get(configs))
                                    .setOutputCapacity(PegasusConfig.PEGASUS_OUTPUT_CAPACITY.get(configs))
                                    .setTimeLimit(PegasusConfig.PEGASUS_TIMEOUT.get(configs))
                                    .addAllServers(servers)
                                    .build();
                            request = request.toBuilder().setConf(jobConfig).build();

                            // todo: process results from pegasus and write to ctx
                            broadcastProcessor.broadcast(request, new IrResultProcessor(new ResultParser() {
                                @Override
                                public List<Object> parseFrom(PegasusClient.JobResponse response) {
                                    return Collections.singletonList(response.getData());
                                }
                            }));

                            ResponseMessage.Builder builder = ResponseMessage.build(msg).code(ResponseStatusCode.SUCCESS);
                            ctx.writeAndFlush(builder.create());
                        }
                    } catch (InvalidProtocolBufferException e) {
                        throw new RuntimeException(e);
                    }
                }).create();
    }
}
