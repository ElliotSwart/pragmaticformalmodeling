---------------------------- MODULE storagecleanerimproved ----------------------------

(***************************************************************************)
(* Server Restart                                                          *)
(***************************************************************************)

ServerRestart(s) ==
    LET currentState == serverStates[s] IN 
    LET terminationTime == (currentState.start + 1) IN
    /\ currentState.state # "waiting" \* Server must be active
    \* This is the only state a server can reach if past termination time
    /\ time => terminationTime
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

(***************************************************************************)
(* Server Writes                                                           *)
(***************************************************************************)

ServerStartWrite(s) ==
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS, m \in METADATAS, i \in IMAGES:
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="started_write",
                                ![s].userId = u, 
                                ![s].metadata = m,
                                ![s].image = i,
                                \* The time a write request starts
                                ![s].start = time
                                ]
        /\ operations' = Append(operations, 
                                    [ 
                                       type |-> "WRITE",
                                       userId |-> u,
                                       metadata |-> m,
                                       image |-> i
                                    ])
    \* Cleaner state needs to be added as unchanged for all server operations
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerStates>>
    /\ UNCHANGED time

ServerWriteBlob(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_write"
    /\ \E id \in UUIDS:
        /\ blobStoreState[id] = [status |-> "UNSET", image |-> "UNSET"]
        /\ blobStoreState' = [blobStoreState EXCEPT 
                                ![id] = [
                                    image |-> currentState.image,
                                    created |-> time
                                    ]]
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="wrote_blob",
                                ![s].imageId = id]
    /\ UNCHANGED <<databaseState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time


ServerWriteMetadataAndReturn(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "wrote_blob"
    /\ databaseState' = [databaseState EXCEPT 
                            ![currentState.userId] = [
                                metadata |-> currentState.metadata, 
                                imageId |-> currentState.imageId] ]

    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<blobStoreState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

ServerFailWrite(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ serverStates[s].state \in {"started_write", "wrote_blob"}
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time


(***************************************************************************)
(* Server Reads                                                            *)
(***************************************************************************)

ServerStartRead(s) ==
    LET currentState == serverStates[s] IN
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS:
                serverStates' = [serverStates EXCEPT
                                    ![s].state ="started_read",
                                    ![s].userId = u,
                                    \* The time a read request starts
                                    ![s].start = time
                                    ]
   
    /\ UNCHANGED <<databaseState, blobStoreState>> 
    /\ UNCHANGED operations
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time


ServerReadMetadata(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata # "UNSET"
    /\ serverStates' = 
        [serverStates EXCEPT
            ![s].state ="read_metadata",
            ![s].metadata = databaseState[currentState.userId].metadata,
            ![s].imageId = databaseState[currentState.userId].imageId]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED operations
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time


ServerReadMetadataAndReturnEmpty(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata = "UNSET"
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
                                            
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> "UNSET",
                               image |-> "UNSET"
                            ])
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time
    
ServerReadBlobAndReturn(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "read_metadata"                               
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> currentState.metadata,
                               image |-> blobStoreState[currentState.imageId].image
                            ])
    /\ serverStates' = [serverStates EXCEPT
                            ![s].state ="waiting",
                            ![s].userId ="UNSET",
                            ![s].metadata = "UNSET",
                            ![s].image = "UNSET",
                            ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

=============================================================================