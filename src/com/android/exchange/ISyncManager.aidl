/*
 * Copyright (C) 2008-2009 Marc Blank
 * Licensed to The Android Open Source Project.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.exchange;

import com.android.exchange.ISyncManagerCallback;
import com.android.exchange.EmailContent;

interface ISyncManager {
    int validate(in String protocol, in String host, in String userName, in String password, int port, boolean ssl) ;

    void registerCallback(ISyncManagerCallback cb);
    void unregisterCallback(ISyncManagerCallback cb);

    boolean startSync(long mailboxId);
    boolean stopSync(long mailboxId);

    boolean updateFolderList(long accountId);

    boolean loadMore(long messageId, ISyncManagerCallback cb);
    boolean loadAttachment(long messageId, in EmailContent.Attachment att, ISyncManagerCallback cb);

    boolean createFolder(long accountId, String name);
    boolean deleteFolder(long accountId, String name);
    boolean renameFolder(long accountId, String oldName, String newName);
    //AddressLookup - real-time address lookup (EAS)
}