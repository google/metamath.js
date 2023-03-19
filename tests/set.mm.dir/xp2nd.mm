include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "c2nd.mm"
include "cfv.mm"
include "elxp.mm"
include "vex.mm"
include "op2ndd.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "adantrl.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem xp2nd
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vc: setvar c


  assert |- ( A e. ( B X. C ) -> ( 2nd ` A ) e. C )

  proof
    cA
    cB
    cC
    cxp
    wcel
    cA
    vb
    cv
    #
    vc
    cv
    #
    cop
    wceq
    #
    @0
    cB
    wcel
    #
    @1
    cC
    wcel
    #
    wa
    wa
    #
    vc
    wex
    vb
    wex
    cA
    c2nd
    cfv
    #
    cC
    wcel
    #
    vb
    vc
    cA
    cB
    cC
    elxp
    @5
    @7
    vb
    vc
    @2
    @4
    @7
    @3
    @2
    @7
    @4
    @2
    @6
    @1
    cC
    @0
    @1
    cA
    vb
    vex
    vc
    vex
    op2ndd
    eleq1d
    biimpar
    adantrl
    exlimivv
    sylbi
end
