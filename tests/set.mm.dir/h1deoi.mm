include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "chil.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "wb.mm"
include "snssi.mm"
include "ocel.mm"
include "mp2b.mm"
include "elexi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "ralsn.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem h1deoi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume h1deot.1: |- B e. ~H


  assert |- ( A e. ( _|_ ` { B } ) <-> ( A e. ~H /\ ( A .ih B ) = 0 ) )

  proof
    cA
    cB
    csn
    #
    cort
    cfv
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    vx
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vx
    @0
    wral
    #
    wa
    #
    @2
    cA
    cB
    csp
    co
    #
    cc0
    wceq
    #
    wa
    cB
    chil
    wcel
    @0
    chil
    wss
    @1
    @7
    wb
    h1deot.1
    cB
    chil
    snssi
    vx
    cA
    @0
    ocel
    mp2b
    @6
    @9
    @2
    @5
    @9
    vx
    cB
    cB
    chil
    h1deot.1
    elexi
    @3
    cB
    wceq
    @4
    @8
    cc0
    @3
    cB
    cA
    csp
    oveq2
    eqeq1d
    ralsn
    anbi2i
    bitri
end
