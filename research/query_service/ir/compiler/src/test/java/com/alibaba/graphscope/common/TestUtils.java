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

package com.alibaba.graphscope.common;

import org.apache.commons.io.FileUtils;

import java.io.File;
import java.net.URL;

public class TestUtils {
    public static byte[] readBytesFromFile(String file) {
        try {
            URL url = TestUtils.class.getClassLoader().getResource(file);
            return FileUtils.readFileToByteArray(new File(url.toURI()));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public static String readJsonFromResource(String file) {
        try {
            URL url = TestUtils.class.getClassLoader().getResource(file);
            return FileUtils.readFileToString(new File(url.toURI()));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
}