include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "c1st.mm"
include "cfv.mm"
include "elxp.mm"
include "vex.mm"
include "op1std.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem xp1st
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vc: setvar c


  assert |- ( A e. ( B X. C ) -> ( 1st ` A ) e. B )

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
    c1st
    cfv
    #
    cB
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
    @3
    @7
    @4
    @2
    @7
    @3
    @2
    @6
    @0
    cB
    @0
    @1
    cA
    vb
    vex
    vc
    vex
    op1std
    eleq1d
    biimpar
    adantrr
    exlimivv
    sylbi
end
