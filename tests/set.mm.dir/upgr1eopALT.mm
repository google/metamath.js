include "wcel.mm"
include "wa.mm"
include "cupgr.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wi.mm"
include "eqid.mm"
include "simpllr.mm"
include "simplrl.mm"
include "wb.mm"
include "eleq2.mm"
include "ad2antrl.mm"
include "mpbird.mm"
include "simplrr.mm"
include "simprr.mm"
include "upgr1e.mm"
include "ex.mm"
include "alrimiv.mm"
include "simpll.mm"
include "snex.mm"
include "a1i.mm"
include "gropeld.mm"

theorem upgr1eopALT
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vg: setvar g


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
    cupgr
    cW
    vg
    cA
    cB
    cC
    cpr
    cop
    #
    csn
    #
    cV
    cvv
    @6
    vg
    cv
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @9
    ciedg
    cfv
    @8
    wceq
    #
    wa
    #
    @9
    cupgr
    wcel
    #
    wi
    vg
    @6
    @13
    @14
    @6
    @13
    wa
    #
    cA
    cB
    cC
    @9
    @10
    cX
    @10
    eqid
    @0
    @1
    @5
    @13
    simpllr
    @15
    cB
    @10
    wcel
    #
    @3
    @2
    @3
    @4
    @13
    simplrl
    @11
    @16
    @3
    wb
    @6
    @12
    @10
    cV
    cB
    eleq2
    ad2antrl
    mpbird
    @15
    cC
    @10
    wcel
    #
    @4
    @2
    @3
    @4
    @13
    simplrr
    @11
    @17
    @4
    wb
    @6
    @12
    @10
    cV
    cC
    eleq2
    ad2antrl
    mpbird
    @6
    @11
    @12
    simprr
    upgr1e
    ex
    alrimiv
    @0
    @1
    @5
    simpll
    @8
    cvv
    wcel
    @6
    @7
    snex
    a1i
    gropeld
end
