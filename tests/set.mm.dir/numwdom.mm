include "cwdom.mm"
include "wbr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "brwdomi.mm"
include "wa.mm"
include "simpr.mm"
include "cfn.mm"
include "0fin.mm"
include "finnum.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "fonum.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "jaodan.mm"
include "sylan2.mm"

theorem numwdom
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( ( A e. dom card /\ B ~<_* A ) -> B e. dom card )

  proof
    cB
    cA
    cwdom
    wbr
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    c0
    wceq
    #
    cA
    cB
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    wo
    cB
    @0
    wcel
    #
    vf
    cB
    cA
    brwdomi
    @1
    @2
    @6
    @5
    @1
    @2
    wa
    cB
    c0
    @0
    @1
    @2
    simpr
    c0
    cfn
    wcel
    c0
    @0
    wcel
    0fin
    c0
    finnum
    ax-mp
    syl6eqel
    @1
    @5
    @6
    @1
    @4
    @6
    vf
    @1
    @4
    @6
    cA
    cB
    @3
    fonum
    ex
    exlimdv
    imp
    jaodan
    sylan2
end
