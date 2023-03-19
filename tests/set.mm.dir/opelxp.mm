include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "elxp2.mm"
include "wb.mm"
include "vex.mm"
include "opth2.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "sylbi.mm"
include "biimprcd.mm"
include "rexlimivv.mm"
include "eqid.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "opeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "impbii.mm"
include "bitri.mm"

theorem opelxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( <. A , B >. e. ( C X. D ) <-> ( A e. C /\ B e. D ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cxp
    wcel
    @0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    cD
    wrex
    vx
    cC
    wrex
    #
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    vx
    vy
    @0
    cC
    cD
    elxp2
    @5
    @8
    @4
    @8
    vx
    vy
    cC
    cD
    @4
    @8
    @1
    cC
    wcel
    #
    @2
    cD
    wcel
    #
    wa
    #
    @4
    cA
    @1
    wceq
    #
    cB
    @2
    wceq
    #
    wa
    @8
    @11
    wb
    cA
    cB
    @1
    @2
    vx
    vex
    vy
    vex
    opth2
    @12
    @6
    @9
    @13
    @7
    @10
    cA
    @1
    cC
    eleq1
    cB
    @2
    cD
    eleq1
    bi2anan9
    sylbi
    biimprcd
    rexlimivv
    @6
    @7
    @0
    @0
    wceq
    #
    @5
    @0
    eqid
    @4
    @14
    @0
    cA
    @2
    cop
    #
    wceq
    vx
    vy
    cA
    cB
    cC
    cD
    @1
    cA
    wceq
    @3
    @15
    @0
    @1
    cA
    @2
    opeq1
    eqeq2d
    @2
    cB
    wceq
    @15
    @0
    @0
    @2
    cB
    cA
    opeq2
    eqeq2d
    rspc2ev
    mp3an3
    impbii
    bitri
end
