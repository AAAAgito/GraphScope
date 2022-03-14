package com.alibaba.maxgraph.servers.ir;

import com.alibaba.graphscope.common.client.RpcChannelFetcher;
import com.alibaba.graphscope.common.config.PegasusConfig;
import com.alibaba.graphscope.common.store.StoreConfigs;
import com.alibaba.graphscope.gremlin.service.IrGremlinServer;
import com.alibaba.graphscope.groot.discovery.DiscoveryFactory;
import com.alibaba.graphscope.groot.discovery.NodeDiscovery;
import com.alibaba.graphscope.groot.frontend.WriteSessionGenerator;
import com.alibaba.graphscope.groot.frontend.write.GraphWriter;
import com.alibaba.graphscope.groot.meta.MetaService;
import com.alibaba.graphscope.groot.rpc.ChannelManager;
import com.alibaba.graphscope.groot.store.StoreService;
import com.alibaba.maxgraph.common.RoleType;
import com.alibaba.maxgraph.common.config.CommonConfig;
import com.alibaba.maxgraph.common.config.Configs;
import com.alibaba.maxgraph.common.config.GremlinConfig;
import com.alibaba.maxgraph.compiler.api.schema.SchemaFetcher;
import com.alibaba.maxgraph.servers.AbstractService;
import com.alibaba.maxgraph.servers.ComputeServiceProducer;
import com.alibaba.maxgraph.servers.gaia.*;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class IrServiceProducer implements ComputeServiceProducer {
    private Configs configs;

    public IrServiceProducer(Configs configs) {
        this.configs = configs;
    }

    @Override
    public AbstractService makeGraphService(
            SchemaFetcher schemaFetcher,
            ChannelManager channelManager,
            NodeDiscovery discovery,
            GraphWriter graphWriter,
            WriteSessionGenerator writeSessionGenerator,
            MetaService metaService) {
        return makeGraphService(schemaFetcher, channelManager);
    }

    @Override
    public AbstractService makeGraphService(
            SchemaFetcher schemaFetcher, ChannelManager channelManager) {
        try {
            int executorCount = CommonConfig.STORE_NODE_COUNT.get(configs);
            RpcChannelFetcher channelFetcher =
                    new RpcChannelManagerFetcher(channelManager, executorCount, RoleType.GAIA_RPC);
            com.alibaba.graphscope.common.config.Configs irConfigs = getConfigs();
            StoreConfigs storeConfigs = new GrootStoreConfigs(configs);

            return new AbstractService() {
                private IrGremlinServer irGremlinServer = new IrGremlinServer(GremlinConfig.GREMLIN_PORT.get(configs));

                @Override
                public void start() {
                    try {
                        irGremlinServer.start(irConfigs, storeConfigs, channelFetcher);
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }

                @Override
                public void stop() {
                    try {
                        irGremlinServer.close();
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }
            };
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public AbstractService makeExecutorService(
            StoreService storeService, MetaService metaService, DiscoveryFactory discoveryFactory) {
        ExecutorEngine executorEngine = new GaiaEngine(configs, discoveryFactory);
        return new GaiaService(configs, executorEngine, storeService, metaService);
    }

    private com.alibaba.graphscope.common.config.Configs getConfigs() {
        Map<String, String> configMap = new HashMap<>();
        configMap.put(
                com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_WORKER_NUM.getKey(),
                String.valueOf(com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_WORKER_NUM.get(configs)));
        configMap.put(
                com.alibaba.graphscope.common.config.PegasusConfig.PEGASUS_TIMEOUT.getKey(),
                String.valueOf(com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_TIMEOUT.get(configs)));
        configMap.put(
                com.alibaba.graphscope.common.config.PegasusConfig.PEGASUS_BATCH_SIZE.getKey(),
                String.valueOf(com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_BATCH_SIZE.get(configs)));
        configMap.put(
                com.alibaba.graphscope.common.config.PegasusConfig.PEGASUS_OUTPUT_CAPACITY.getKey(),
                String.valueOf(com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_OUTPUT_CAPACITY.get(configs)));
        configMap.put(
                PegasusConfig.PEGASUS_MEMORY_LIMIT.getKey(),
                String.valueOf(com.alibaba.maxgraph.servers.gaia.PegasusConfig.PEGASUS_MEMORY_LIMIT.get(configs)));
        return new com.alibaba.graphscope.common.config.Configs(configMap);
    }
}
