-- 3-hop, nack-free, invalidation protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount: 2;
  VC1: 0;                -- low priority
  VC2: 1;
  VC3: 2;                
  VC3: 3;
  QMax: 2;
  NumVCs: VC3 - VC0 + 1;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc }; -- arbitrary values for tracking coherence
  Value: scalarset(ValueCount); -- need enumeration for IsMember calls

  VCType: VC0..NumVCs-1;

  MessageType: enum {  GetS,         
                       FwdGetS,      
                       GetSAck,         
                       FwdGetSAck,      
		                   GetSFwd,        

		                   GetM,        
                       FwdGetM,    
                       GetMAck,       
                       FwdGetMAck,    
		                   GetMFwd,      
                      
		                   WBReq,           
                       WBAck,           
                       WBStaleReadAck,  
                       WBStaleWriteAck, 
 
                       InvReq,         
                       InvAck            
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- don't need a destination for verification
      vc: VCType;
      aux: Node;  -- participating node (used when forwarding msgs)
      val: Value;
      cnt: 0..ProcCount;
    End;

  HomeState:
    Record
      state: enum { HM, HS, HI, TMM, TSD };
      owner: Node;	
      pending_node: Node;
      sharers: multiset [ProcCount] of Node; 
      val:Value;
    End;

  ProcState:
    Record
      state: enum { PM, PS, PI,
                    TIS, TIL,        
		                IM, IIM, TRIS, TRIF, TMI, TMII, TWIS, TWIF    
                                    
                  };
    count1: 0..ProcCount;
    count2: 0..ProcCount;                 
    val:Value;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
  msg_processed: boolean;
  LastWrite: Value;

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
               vc:VCType;
	       aux:Node;
               val:Value;
               cnt:0..ProcCount);
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.val   := val;
  msg.cnt   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  switch msg.mtype
  case GetM, GetS, WBReq:
    msg_processed := false;  -- we can receive a raw request any time
  else
    error "Unhandled message type!";
  endswitch;
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then
        Send(InvReq, n, HomeType, VC3, rqst,HomeNode.val, UNDEFINED);
      endif;
      RemoveFromSharersList(n);
    endif;
  endfor;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var cnthack:0..1;  -- subtracted from InvReq count to get around compiler
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);

  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) != 0
  then 
    cnthack := 1;
  else
    cnthack := 0;
  endif;

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HI:
    Assert (cnt = 0) "Invalid implies empty sharer list";

    switch msg.mtype

    case GetS:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      Send(GetSAck, msg.src, HomeType, VC3, UNDEFINED,HomeNode.val,UNDEFINED);

    case GetM:
      HomeNode.state := HM;
      HomeNode.owner := msg.src;
      HomeNode.val   := msg.val;
      Send(GetMAck, msg.src, HomeType, VC3, UNDEFINED,HomeNode.val,cnt); -- cnt is zero

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HM:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "Modified must have owner";

    switch msg.mtype

    case GetS:
      HomeNode.state := TSD; 
      AddToSharersList(msg.src);    
      HomeNode.pending_node := msg.src;
      Send(FwdGetS, HomeNode.owner, HomeType, VC3, msg.src,UNDEFINED,UNDEFINED);
      
    case GetM:
      HomeNode.state := TMM;
      HomeNode.pending_node := msg.src;
      HomeNode.val   := msg.val;
      Send(FwdGetM, HomeNode.owner, HomeType, VC3, msg.src,UNDEFINED,UNDEFINED);
      
    case WBReq:
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HI;
      HomeNode.val   := msg.val;
      HomeNode.owner := UNDEFINED;
      Send(WBAck, msg.src, HomeType, VC3, UNDEFINED,UNDEFINED,UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HS:
    Assert (cnt != 0) "Share implies non empty sharer list";

    switch msg.mtype

    case GetS:
      AddToSharersList(msg.src);
      Send(GetSAck, msg.src, HomeType, VC3, UNDEFINED,HomeNode.val,UNDEFINED);

    case GetM:
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HM;
      --HomeNode.owner := UNDEFINED;
      HomeNode.val   := msg.val;
      Send(GetMAck, msg.src, HomeType, VC3, UNDEFINED,UNDEFINED,cnt-cnthack);        
      SendInvReqToSharers(msg.src); -- removes sharers, too
      HomeNode.owner := msg.src;
      
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case TSD:
    switch msg.mtype

    case FwdGetSAck:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      --AddToSharersList(msg.aux);
      HomeNode.val := msg.val;
      undefine HomeNode.owner;
    
    case WBReq:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HS;
      HomeNode.val   := msg.val;
      AddToSharersList(HomeNode.pending_node);
      Send(WBStaleReadAck, msg.src, HomeType, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
      undefine HomeNode.owner;
      undefine HomeNode.pending_node;
    
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
      
  case TMM:
    switch msg.mtype

    case FwdGetMAck:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HM;
      HomeNode.owner := HomeNode.pending_node;
      undefine HomeNode.pending_node;

    case WBReq:
      if HomeNode.owner = msg.src
      then
        -- old owner
        Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
	Send(WBStaleWriteAck, msg.src, HomeType, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
	HomeNode.state := HM;
	HomeNode.owner := HomeNode.pending_node;
	--HomeNode.val   := msg.val;
	undefine HomeNode.pending_node;
      elsif HomeNode.pending_node = msg.src
      then
        -- new owner, queue or nack
	msg_processed := false;
      else
        error "WBReq from unexpected node";
      endif;

    else
      ErrorUnhandledMsg(msg, HomeType);
    
    endswitch;

  endswitch;

End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val   do
  switch ps
  case PI:

    switch msg.mtype
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PM:

    switch msg.mtype
    case FwdGetM:
      Send(FwdGetMAck, HomeType, p, VC3, UNDEFINED,pv,UNDEFINED);
      Send(GetMFwd, msg.aux, p, VC3, UNDEFINED,pv,UNDEFINED);
      ps := PI;
    case FwdGetS:
      Send(FwdGetSAck, HomeType, p, VC3, UNDEFINED,pv, UNDEFINED);
      Send(GetSFwd, msg.aux, p, VC3, UNDEFINED,pv, UNDEFINED);
      ps := PS;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:

    switch msg.mtype
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
      ps := PI;
      pv := msg.val;
    --  LastWrite := msg.val;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case IM:
    
    switch msg.mtype
    case GetMFwd:
      pv := msg.val;
      ps := PM;
    case GetMAck:
      Procs[p].count2 := msg.cnt;
      if Procs[p].count1 = Procs[p].count2
      then
	      ps := PM;
             -- pv := msg.val;
              LastWrite := pv;
	      undefine Procs[p].count1;
	      undefine Procs[p].count2;
      else
        ps := IIM;
      endif;
    case InvAck:
      Procs[p].count1 := Procs[p].count1 + 1;
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED, UNDEFINED,UNDEFINED);
    case FwdGetS, FwdGetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case IIM:

    switch msg.mtype
    case InvAck:
      Procs[p].count1 := Procs[p].count1 + 1;
      if Procs[p].count1 = Procs[p].count2
      then
	      ps := PM;
              LastWrite := pv;
	      undefine Procs[p].count1;
	      undefine Procs[p].count2;
      endif
    case FwdGetS, FwdGetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TIS:

    switch msg.mtype
    case GetSAck, GetSFwd:
      pv := msg.val;
      ps := PS;
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED, UNDEFINED,UNDEFINED);
      ps := TIL;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TIL:
   
    switch msg.mtype
    case GetSAck, GetSFwd:
      ps := PI;
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMI:

    switch msg.mtype
    case WBAck:
      ps := PI;
    case InvReq:
      Send(InvAck, msg.aux, p, VC3, UNDEFINED,UNDEFINED,UNDEFINED);
      ps := TMII;
    case WBStaleReadAck:
      ps := TRIS;
    case FwdGetS:
      Send(GetSFwd, msg.aux, p, VC3, UNDEFINED,pv,UNDEFINED);
      ps := TRIF;
    case WBStaleWriteAck:
      ps := TWIS;
    case FwdGetM:
      Send(GetMFwd, msg.aux, p, VC3, UNDEFINED,pv,UNDEFINED);
      ps := TWIF;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMII:
    switch msg.mtype
    case WBAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIS:
    switch msg.mtype
    case FwdGetS:
      ps := PI;
      Send(GetSFwd, msg.aux, p, VC3, UNDEFINED,pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIF:
    switch msg.mtype
    case WBStaleReadAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIS:
    switch msg.mtype
    case FwdGetM:
      ps := PI;
      Send(GetMFwd, msg.aux, p, VC3, UNDEFINED, pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIF:
    switch msg.mtype
    case WBStaleWriteAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
 
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc Do
  alias p:Procs[n] Do
  
  ruleset v:Value Do 
  rule "read request PI"
    p.state = PI 
  ==>
    Send(GetS, HomeType, n, VC1, UNDEFINED,UNDEFINED,UNDEFINED);
    p.state := TIS;
  endrule;

  rule "read request PS"
    p.state = PS 
  ==>
    p.state := PS;
  endrule;

  rule "read request PM"
    p.state = PM 
  ==>
    p.state := PM
  endrule;

  rule "write request PI"
    (p.state = PI)
  ==>
    Send(GetM, HomeType, n, VC1, UNDEFINED,v, UNDEFINED);
    p.state := IM;
    p.val   := v;
    clear p.count1;
    clear p.count2;
  endrule;

  rule "write request PM"
    (p.state = PM)
  ==>
    p.val := v;
    LastWrite := v;
  endrule;

  rule "write request PS"
    (p.state = PS)
  ==>
    Send(GetM, HomeType, n, VC1, UNDEFINED,v,UNDEFINED);
    p.state := IM;  -- collapsing states from Nikos' diagrams
    p.val   := v;
    clear p.count1;
    clear p.count2;
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, VC3, UNDEFINED,p.val,UNDEFINED);  -- fixme
    p.state := TMI;
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    p.state := PI;
  endrule;
  
  endruleset;
  endalias;

endruleset;

-- receive rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = VC3) |
      (msg.vc = VC2 & MultiSetCount(m:chan, chan[m].vc = VC3)  = 0) |
      (msg.vc = VC1 & MultiSetCount(m:chan, chan[m].vc = VC3)  = 0 
                    & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0) |
      (msg.vc = VC0 & MultiSetCount(m:chan, chan[m].vc = VC3)  = 0 
                    & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0
                    & MultiSetCount(m:chan, chan[m].vc = VC1)  = 0)
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);

	if msg_processed
	then
	  MultiSetRemove(midx, chan);
	endif;

      else
        ProcReceive(msg, n);

	if msg_processed
	then
	  MultiSetRemove(midx, chan);
	endif;
	  
      endif;

    endrule;
  
    endalias;
    endalias;
  endchoose;  
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
For v:Value do
  -- home node initialization
  HomeNode.state := HI;
  undefine HomeNode.sharers;
  undefine HomeNode.owner;
  undefine HomeNode.pending_node;
  undefine HomeNode.sharers;
  HomeNode.val := v;
  endfor;
LastWrite := HomeNode.val;
  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
    clear Procs[i].count2;
    clear Procs[i].count1;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "modified w/ empty sharers list"
  HomeNode.state = HM
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0 ;

invariant "Invalid Implies empty owner"
  HomeNode.state =HI
    ->
      IsUndefined(HomeNode.owner);

invariant "values in valid state match last write"
  Forall n: Proc Do
    Procs[n].state = PS | Procs[n].state =PM
    ->
      Procs[n].val=LastWrite
  end;

invariant "modified implies empty sharers list"
  HomeNode.state=HM
  ->
    MultiSetCount(i:HomeNode.sharers,true)=0;

invariant "Invalid implies empty sharer list"
  HomeNode.state=HI
  ->
    MultiSetCount(i:HomeNode.sharers, true)=0;

invariant "values in memory matches value of last write when shared or invalid"
  Forall n:Proc Do
    HomeNode.state=HS | HomeNode.state=HI
    ->
      HomeNode.val=LastWrite
  end;

invariant "values in shared state match memory"
  Forall n:Proc Do
    HomeNode.state=HS & Procs[n].state=PS
    ->
      HomeNode.val=Procs[n].val
  end;

invariant "modified implies empty sharers list"
  HomeNode.state=HM
  ->
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = HI
  -> 
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n: Proc Do
    HomeNode.state = HS | HomeNode.state = HI
    -> 
      HomeNode.val = LastWrite
  end;

invariant "value in shared state match memory"
  Forall n : Proc Do
    HomeNode.state=HS & Procs[n].state = PS
    -> 
      HomeNode.val = Procs[n].val
  end;

invariant "modified implies empty sharers list"
  HomeNode.state = HI
  -> 
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n: Proc Do
    HomeNode.state=HS |HomeNode.state = HI
    ->
      HomeNode.val=LastWrite
  end;

invariant "values in shared state match memory"
  Forall n: Proc Do
    HomeNode.state = HS &Procs[n].state= PS
    ->
      HomeNode.val=Procs[n].val
  end;

