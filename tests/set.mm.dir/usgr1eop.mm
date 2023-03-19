include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "cusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "eqid.mm"
include "simpllr.mm"
include "simplrl.mm"
include "cvv.mm"
include "wceq.mm"
include "simpl.mm"
include "adantr.mm"
include "snex.mm"
include "a1i.mm"
include "opvtxfv.mm"
include "syl2an.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "ciedg.mm"
include "opiedgfv.mm"
include "simpr.mm"
include "usgr1e.mm"
include "ex.mm"

theorem usgr1eop
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( ( V e. W /\ A e. X ) /\ ( B e. V /\ C e. V ) ) -> ( B =/= C -> <. V , { <. A , { B , C } >. } >. e. USGraph ) )

  proof
    cV
    cW
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    wa
    #
    cB
    cC
    wne
    #
    cV
    cA
    cB
    cC
    cpr
    cop
    #
    csn
    #
    cop
    #
    cusgr
    wcel
    @6
    @7
    wa
    #
    cA
    cB
    cC
    @10
    @10
    cvtx
    cfv
    #
    cX
    @12
    eqid
    @0
    @1
    @5
    @7
    simpllr
    @11
    cB
    cV
    @12
    @2
    @3
    @4
    @7
    simplrl
    @6
    @0
    @9
    cvv
    wcel
    #
    @12
    cV
    wceq
    #
    @7
    @2
    @0
    @5
    @0
    @1
    simpl
    #
    adantr
    #
    @13
    @7
    @8
    snex
    #
    a1i
    #
    @9
    cV
    cW
    cvv
    opvtxfv
    #
    syl2an
    eleqtrrd
    @6
    cC
    @12
    wcel
    @7
    @6
    cC
    cV
    @12
    @2
    @3
    @4
    simprr
    @2
    @0
    @13
    @14
    @5
    @15
    @13
    @5
    @17
    a1i
    @19
    syl2an
    eleqtrrd
    adantr
    @6
    @0
    @13
    @10
    ciedg
    cfv
    @9
    wceq
    @7
    @16
    @18
    @9
    cV
    cW
    cvv
    opiedgfv
    syl2an
    @6
    @7
    simpr
    usgr1e
    ex
end
