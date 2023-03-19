include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "ssexg.mm"
include "3adant1.mm"
include "restco.mm"
include "syl3anc.mm"
include "simp2.mm"
include "sseqin2.mm"
include "sylib.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem restabs
  let cS: class S
  let cT: class T
  let cJ: class J
  let cV: class V
  let cW: class W


  assert |- ( ( J e. V /\ S C_ T /\ T e. W ) -> ( ( J |`t T ) |`t S ) = ( J |`t S ) )

  proof
    cJ
    cV
    wcel
    #
    cS
    cT
    wss
    #
    cT
    cW
    wcel
    #
    w3a
    #
    cJ
    cT
    crest
    co
    cS
    crest
    co
    #
    cJ
    cT
    cS
    cin
    #
    crest
    co
    #
    cJ
    cS
    crest
    co
    @3
    @0
    @2
    cS
    cvv
    wcel
    #
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @1
    @2
    @7
    @0
    cS
    cT
    cW
    ssexg
    3adant1
    cT
    cS
    cJ
    cV
    cW
    cvv
    restco
    syl3anc
    @3
    @5
    cS
    cJ
    crest
    @3
    @1
    @5
    cS
    wceq
    @0
    @1
    @2
    simp2
    cS
    cT
    sseqin2
    sylib
    oveq2d
    eqtrd
end
