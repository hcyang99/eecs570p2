
-- two-state 4-hop VI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  QMax: 2;
  NumVCs: VC2 - VC0 + 1;
  NetMax: 10;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };
  ProcCountType: 0..ProcCount;

  VCType: VC0..NumVCs-1;

  MessageType: enum {  
                      GetS,
                      GetSAck,
                      GetEAck,
                      GetM,
                      GetMAck,
                      Upgrade,
                      UpgradeAck,
                      PutS,
                      PutSAck,
                      PutM,
                      PutMAck,
                      ModE,
                      ModEAck,
                      PutE,
                      PutEAck,
                      WB,
                      WBAck,
                      Inv,
                      InvAck,
                      NAck
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value;
      reqsrc: Node;
    End;

  HomeState:
    Record
      state: enum { 
										H_Modified, 								-- steady state: M
										H_Shared,										-- steady state: S
										H_Invalid, 									-- steady state: I
                    H_Exclusive,                -- steady state: E

                    HT_SS_GetS,
                    HT_MM_GetM,
                    HT_MS,
                    HT_SM_GetM,
                    HT_SM_Upgrade,
                    HT_ES,
                    HT_EM,
                    HT_ME
									}; 														--transient states during recall
      owner: Node;
      newOwner: Node;
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      mshr: multiset [ProcCount] of Node;
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { 
                    P_Modified,
                    P_Shared,
                    P_Invalid,
                    P_Exclusive,

                    PT_IM,
                    PT_MI,

                    PT_IS,
                    PT_SI,

                    PT_SM,

                    PT_EI,
                    PT_EM,
                    PT_ME
                  };
      val: Value;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
         reqsrc: Node;
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.reqsrc := reqsrc;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;


-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure AddToMSHR(n:Node);
Begin
  if MultiSetCount(i:HomeNode.mshr, HomeNode.mshr[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.mshr);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0 
End;

Function CountMSHR() : ProcCountType;
Begin
  return MultiSetCount(i:HomeNode.mshr, true);
End;

Function CountSharers() : ProcCountType;
Begin
  return MultiSetCount(i:HomeNode.sharers, true);
End;

Function CountModified() : ProcCountType;
var ret: ProcCountType;
Begin
  ret := 0;
  for n:Proc do
    if Procs[n].state = P_Modified
    then 
      ret := ret + 1;
    endif;
  endfor;
  return ret;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure RemoveFromMSHR(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.mshr, HomeNode.mshr[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here 
        Send(Inv, n, HomeType, VC1, UNDEFINED, rqst);
      endif;
    endif;
  endfor;
End;

Procedure ForwardReqToSharers(rqst:Node; reqType: MessageType);
var flag: Boolean;
Begin
  flag := false;
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here 
        if (flag = false)
        then
          flag := true;
          Send(reqType, n, HomeType, VC1, UNDEFINED, rqst);
          AddToMSHR(n);
        endif;
      endif;
    endif;
  endfor;
End;

Procedure CopySharersToMSHR();
Begin
  undefine HomeNode.mshr;
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      MultiSetAdd(n, HomeNode.mshr);
    endif;
  endfor;
End;



Procedure HomeReceive(msg:Message);
var cnt:ProcCountType;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_Invalid:
    switch msg.mtype

    case GetS:
      HomeNode.state := H_Exclusive;
      HomeNode.owner := msg.src;
      Send(GetEAck, msg.src, HomeType, VC2, HomeNode.val, msg.reqsrc);
    
    case GetM:
      HomeNode.state := H_Modified;
      HomeNode.owner := msg.src;
      Send(GetMAck, msg.src, HomeType, VC2, HomeNode.val, msg.reqsrc);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Modified:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "HomeNode has no owner, but line is Modified";

    switch msg.mtype
    case GetS:
      HomeNode.state := HT_MS;    
      AddToSharersList(HomeNode.owner);
      AddToSharersList(msg.src);
      Send(GetS, HomeNode.owner, HomeType, VC1, UNDEFINED, msg.src);
            
    case PutM:
    	assert (msg.src = HomeNode.owner) "Writeback from non-owner";
      HomeNode.state := H_Invalid;
      HomeNode.val := msg.val;
      Send(PutMAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
      undefine HomeNode.owner;

    case GetM:
      assert (msg.src != HomeNode.owner) "GetM involked by owner";
      HomeNode.state := HT_MM_GetM;
      HomeNode.newOwner := msg.src;
      Send(Inv, HomeNode.owner, HomeType, VC1, UNDEFINED, msg.src);

    case WB:
      assert(HomeNode.owner = msg.src)
        "WB called from non-owner";
      HomeNode.state := H_Exclusive;
      HomeNode.val := msg.val;
      Send(WBAck, HomeNode.owner, HomeType, VC2, UNDEFINED, msg.src);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Shared:
    switch msg.mtype
    case GetM:
      assert(!IsSharer(msg.src))
        "GetM called from sharer";
      HomeNode.state := HT_SM_GetM;
      HomeNode.newOwner := msg.src;
      Send(GetMAck, msg.src, HomeType, VC2, HomeNode.val, msg.reqsrc);
      SendInvReqToSharers(msg.src);
      CopySharersToMSHR();

    case Upgrade:
      assert(IsSharer(msg.src))
        "Upgrade called from non-sharer";
    	HomeNode.state := HT_SM_Upgrade;
      HomeNode.newOwner := msg.src;
      Send(UpgradeAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
      SendInvReqToSharers(msg.src);
      CopySharersToMSHR();
      RemoveFromMSHR(msg.src);

    case PutS:
      RemoveFromSharersList(msg.src);
      if (cnt = 1)
      then
        HomeNode.state := H_Invalid;
      endif;
      Send(PutSAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
      
    case GetS:
      ForwardReqToSharers(msg.src, GetS);
      AddToSharersList(msg.src);
      HomeNode.state := HT_SS_GetS;

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  
  case H_Exclusive:
    switch msg.mtype
    case GetM:
      if (msg.src != HomeNode.owner)
      then
        HomeNode.state := HT_EM;
        HomeNode.newOwner := msg.src;
        Send(Inv, HomeNode.owner, HomeType, VC1, UNDEFINED, msg.reqsrc);
      else 
        HomeNode.state := H_Modified;
        Send(GetMAck, HomeNode.owner, HomeType, VC2, UNDEFINED, msg.reqsrc);
      endif;
    case GetS:
      assert(HomeNode.owner != msg.src)
        "GetS called from exclusive owner";
      HomeNode.state := HT_ES;
      AddToSharersList(HomeNode.owner);
      AddToSharersList(msg.src);
      Send(GetS, HomeNode.owner, HomeType, VC1, UNDEFINED, msg.src);
    case ModE:
      assert(HomeNode.owner = msg.src)
        "ModE called from non-owner";
      HomeNode.state := H_Modified;
      Send(ModEAck, msg.src, HomeType, VC2, UNDEFINED, msg.src);

    case PutE:
      assert(HomeNode.owner = msg.src)
        "PutE called from non-owner";
      HomeNode.state := H_Invalid;
      undefine HomeNode.owner;
      Send(PutEAck, msg.src, HomeType, VC2, UNDEFINED, msg.src);

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  
  case HT_ES:
    switch msg.mtype
    case GetSAck:
      undefine HomeNode.owner;
      HomeNode.state := H_Shared;
    
    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case ModE:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutE:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    case PutS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case Upgrade:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_EM:
    switch msg.mtype
    case InvAck:
      assert(HomeNode.owner = msg.src)
        "InvAck to HomeNode from non-owner";
      HomeNode.owner := HomeNode.newOwner;
      undefine HomeNode.newOwner;
      HomeNode.state := H_Modified;
    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case ModE:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutE:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_MM_GetM:
    switch msg.mtype
    case InvAck:
      assert(msg.src = HomeNode.owner) "InvAck from non-owner";
      HomeNode.owner := HomeNode.newOwner;
      undefine HomeNode.newOwner;
      HomeNode.state := H_Modified;

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case WB:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_SS_GetS:
    switch msg.mtype
    case GetSAck:
      RemoveFromMSHR(msg.src);
      if (CountMSHR() = 0)
      then
        AddToSharersList(msg.reqsrc);
        HomeNode.state := H_Shared;
      endif;
    
    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    case Upgrade:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_MS:
    switch msg.mtype
    case GetSAck:
      undefine HomeNode.owner;
      HomeNode.state := H_Shared;
      HomeNode.val := msg.val;
    
    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    case PutM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    case Upgrade:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case WB:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
    
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HT_SM_GetM:
    switch msg.mtype
    case InvAck:
      RemoveFromMSHR(msg.src);
      if CountMSHR() = 0
      then
        undefine HomeNode.mshr;
        undefine HomeNode.sharers;
        HomeNode.owner := HomeNode.newOwner;
        undefine HomeNode.newOwner;
        HomeNode.state := H_Modified;
      endif;

    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case Upgrade:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case WB:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_SM_Upgrade:
    switch msg.mtype
    case InvAck:
      RemoveFromMSHR(msg.src);
      if CountMSHR() = 0
      then
        undefine HomeNode.mshr;
        undefine HomeNode.sharers;
        HomeNode.owner := HomeNode.newOwner;
        undefine HomeNode.newOwner;
        HomeNode.state := H_Modified;
      endif;

    case GetS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case GetM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutS:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case PutM:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case Upgrade:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case WB:
      Send(NAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

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
  alias pv:Procs[p].val do

  switch ps
  case P_Modified:

    switch msg.mtype
    case GetS:
      Send(GetSAck, msg.reqsrc, p, VC2, pv, msg.reqsrc);
      Send(GetSAck, HomeType, p, VC2, pv, msg.reqsrc);
      ps := P_Shared;
    case Inv:
      Send(InvAck,HomeType, p, VC2, pv, msg.reqsrc);
      ps := P_Invalid;
      undefine pv;
    case NAck:
      ps := ps;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case P_Shared:

    switch msg.mtype
    case Inv:
      Send(InvAck, HomeType, p, VC2, UNDEFINED, msg.reqsrc);
      undefine pv;
      ps := P_Invalid;

    case GetS:
      Send(GetSAck, HomeType, p, VC2, pv, msg.reqsrc);
      Send(GetSAck, msg.reqsrc, p, VC2, pv, msg.reqsrc);

    case NAck:
    	ps := ps;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  case P_Invalid:    

    switch msg.mtype
    case NAck:
    	ps := ps;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_Exclusive:
    switch msg.mtype
    case GetS:
      Send(GetSAck, HomeType, p, VC2, pv, msg.reqsrc);
      Send(GetSAck, msg.reqsrc, p, VC2, pv, msg.reqsrc);
      ps := P_Shared;

    case Inv:
      Send(InvAck, HomeType, p, VC2, pv, msg.reqsrc);
      undefine pv;
      ps := P_Invalid;
  
    case NAck:
      ps := ps;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  
  case PT_EI:
    switch msg.mtype
    case PutEAck:
      undefine pv;
      ps := P_Invalid;
    case NAck:
      ps := P_Exclusive;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_EM:
    switch msg.mtype
    case GetMAck:
      ps := P_Modified;
    case NAck:
      ps := P_Exclusive;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_ME:
    switch msg.mtype
    case WBAck:
      ps := P_Exclusive;
    case NAck:
      ps := P_Modified;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;
      

  case PT_IM:
    switch msg.mtype
    case GetMAck:
      assert(msg.reqsrc = p) "Received other's GetMAck";
      pv := msg.val;
      ps := P_Modified;
    case NAck:
      ps := P_Invalid;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  
  case PT_IS:
    switch msg.mtype
    case GetSAck:
      assert(msg.reqsrc = p) "Received other's GetSAck";
      pv := msg.val;
      ps := P_Shared;
    case GetEAck:
      assert(msg.reqsrc = p) "Received other's GetEAck";
      pv := msg.val;
      ps := P_Exclusive;
    case NAck:
      ps := P_Invalid;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_SI:
    switch msg.mtype
    case PutSAck:
      undefine pv;
      ps := P_Invalid;
    case NAck:
      ps := P_Shared;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_SM:
    switch msg.mtype
    case UpgradeAck:
      ps := P_Modified;
    case NAck:
      ps := P_Shared;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;
  
  case PT_MI:
    switch msg.mtype
    case PutMAck:
      ps := P_Invalid;
      undefine pv;
    case NAck:
      ps := P_Modified;
    case Inv:
      msg_processed := false;
    case GetS:
      msg_processed := false;
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
  	rule "Store Hit"
   	 (p.state = P_Modified)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "Load Miss"
    p.state = P_Invalid 
  ==>
    Send(GetS, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_IS;
  endrule;

  rule "Store Miss"
    p.state = P_Invalid 
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_IM;
  endrule;

  rule "Store Hit No Permission"
    p.state = P_Shared
  ==>
    Send(Upgrade, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_SM;
  endrule;

  rule "Evict Shared"
    p.state = P_Shared
  ==>
    Send(PutS, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_SI;
  endrule;

  rule "Evict Modified"
    p.state = P_Modified
  ==>
    Send(PutM, HomeType, n, VC0, p.val, n);
    p.state := PT_MI;
  endrule;

  rule "Evict Exclusive"
    p.state = P_Exclusive
  ==>
    Send(PutE, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_EI;
  endrule;

  rule "Store to Exclusive"
    p.state = P_Exclusive
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, n);
    p.state := PT_EM;
  endrule;

  rule "Self Downgrade"
    p.state = P_Modified
  ==>
    Send(WB, HomeType, n, VC0, p.val, n);
    p.state := PT_ME;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_Invalid;
  undefine HomeNode.owner;
  undefine HomeNode.newOwner;
  undefine HomeNode.sharers;
  undefine HomeNode.mshr;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_Invalid
    ->
      IsUndefined(HomeNode.owner);

-- invariant "value in memory matches value of last write, when invalid"
--      HomeNode.state = H_Invalid 
--     ->
-- 			HomeNode.val = LastWrite;

-- invariant "values in valid state match last write"
--   Forall n : Proc Do	
--      Procs[n].state = P_Valid
--     ->
-- 			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
-- 	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
    ->
			IsUndefined(Procs[n].val)
	end;
	

-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = H_Modified
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_Invalid
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Exclusive implies empty sharer list"
  HomeNode.state = H_Exclusive
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid or exclusive"
  Forall n : Proc Do	
     HomeNode.state = H_Shared | HomeNode.state = H_Invalid | HomeNode.state = H_Exclusive
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Shared & Procs[n].state = P_Shared
    ->
			HomeNode.val = Procs[n].val
	end;

invariant "values in exclusive state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Exclusive & Procs[n].state = P_Exclusive
    ->
			HomeNode.val = Procs[n].val
	end;

invariant "only one write permission"
  HomeNode.state = H_Modified
    ->
      CountModified() <= 1;

