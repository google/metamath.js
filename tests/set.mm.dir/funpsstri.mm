include "wfun.mm"
include "wss.mm"
include "wa.mm"
include "cdm.mm"
include "wo.mm"
include "w3a.mm"
include "wpss.mm"
include "wceq.mm"
include "w3o.mm"
include "cres.mm"
include "wi.mm"
include "funssres.mm"
include "ex.mm"
include "anim12d.mm"
include "ssres2.mm"
include "orim12i.mm"
include "sseq12.mm"
include "wb.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "syl5ib.mm"
include "syl6.mm"
include "3imp.mm"
include "sspsstri.mm"
include "sylib.mm"

theorem funpsstri
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- ( ( Fun H /\ ( F C_ H /\ G C_ H ) /\ ( dom F C_ dom G \/ dom G C_ dom F ) ) -> ( F C. G \/ F = G \/ G C. F ) )

  proof
    cH
    wfun
    #
    cF
    cH
    wss
    #
    cG
    cH
    wss
    #
    wa
    #
    cF
    cdm
    #
    cG
    cdm
    #
    wss
    #
    @5
    @4
    wss
    #
    wo
    #
    w3a
    cF
    cG
    wss
    #
    cG
    cF
    wss
    #
    wo
    #
    cF
    cG
    wpss
    cF
    cG
    wceq
    cG
    cF
    wpss
    w3o
    @0
    @3
    @8
    @11
    @0
    @3
    cH
    @4
    cres
    #
    cF
    wceq
    #
    cH
    @5
    cres
    #
    cG
    wceq
    #
    wa
    #
    @8
    @11
    wi
    @0
    @1
    @13
    @2
    @15
    @0
    @1
    @13
    cH
    cF
    funssres
    ex
    @0
    @2
    @15
    cH
    cG
    funssres
    ex
    anim12d
    @8
    @12
    @14
    wss
    #
    @14
    @12
    wss
    #
    wo
    @16
    @11
    @6
    @17
    @7
    @18
    @4
    @5
    cH
    ssres2
    @5
    @4
    cH
    ssres2
    orim12i
    @16
    @17
    @9
    @18
    @10
    @12
    cF
    @14
    cG
    sseq12
    @15
    @13
    @18
    @10
    wb
    @14
    cG
    @12
    cF
    sseq12
    ancoms
    orbi12d
    syl5ib
    syl6
    3imp
    cF
    cG
    sspsstri
    sylib
end
