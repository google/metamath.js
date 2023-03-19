include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "opeq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "bibi12d.mm"
include "opeq2.mm"
include "anbi2d.mm"
include "vex.mm"
include "opth.mm"
include "vtocl2g.mm"

theorem opthg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cC
    cD
    cop
    #
    wceq
    #
    @0
    cC
    wceq
    #
    @1
    cD
    wceq
    #
    wa
    #
    wb
    cA
    @1
    cop
    #
    @3
    wceq
    #
    cA
    cC
    wceq
    #
    @6
    wa
    #
    wb
    cA
    cB
    cop
    #
    @3
    wceq
    #
    @10
    cB
    cD
    wceq
    #
    wa
    #
    wb
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    #
    @4
    @9
    @7
    @11
    @16
    @2
    @8
    @3
    @0
    cA
    @1
    opeq1
    eqeq1d
    @16
    @5
    @10
    @6
    @0
    cA
    cC
    eqeq1
    anbi1d
    bibi12d
    @1
    cB
    wceq
    #
    @9
    @13
    @11
    @15
    @17
    @8
    @12
    @3
    @1
    cB
    cA
    opeq2
    eqeq1d
    @17
    @6
    @14
    @10
    @1
    cB
    cD
    eqeq1
    anbi2d
    bibi12d
    @0
    @1
    cC
    cD
    vx
    vex
    vy
    vex
    opth
    vtocl2g
end
