include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "cvtx.mm"
include "cfv.mm"
include "eqid.mm"
include "simplr.mm"
include "simpl.mm"
include "adantl.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "a1i.mm"
include "opvtxfv.mm"
include "syl2an.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "ciedg.mm"
include "opiedgfv.mm"
include "upgr1e.mm"

theorem upgr1eop
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( ( V e. W /\ A e. X ) /\ ( B e. V /\ C e. V ) ) -> <. V , { <. A , { B , C } >. } >. e. UPGraph )

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
    cA
    cB
    cC
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
    @9
    cvtx
    cfv
    #
    cX
    @10
    eqid
    @0
    @1
    @5
    simplr
    @6
    cB
    cV
    @10
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @2
    @0
    @8
    cvv
    wcel
    #
    @10
    cV
    wceq
    @5
    @0
    @1
    simpl
    #
    @11
    @5
    @7
    snex
    a1i
    #
    @8
    cV
    cW
    cvv
    opvtxfv
    syl2an
    #
    eleqtrrd
    @6
    cC
    cV
    @10
    @2
    @3
    @4
    simprr
    @14
    eleqtrrd
    @2
    @0
    @11
    @9
    ciedg
    cfv
    @8
    wceq
    @5
    @12
    @13
    @8
    cV
    cW
    cvv
    opiedgfv
    syl2an
    upgr1e
end
