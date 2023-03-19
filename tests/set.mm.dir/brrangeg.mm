include "cv.mm"
include "crange.mm"
include "wbr.mm"
include "crn.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "rneq.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "eqeq1.mm"
include "vex.mm"
include "brrange.mm"
include "vtocl2g.mm"

theorem brrangeg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> ( A Range B <-> B = ran A ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    crange
    wbr
    #
    @1
    @0
    crn
    #
    wceq
    #
    wb
    cA
    @1
    crange
    wbr
    #
    @1
    cA
    crn
    #
    wceq
    #
    wb
    cA
    cB
    crange
    wbr
    #
    cB
    @6
    wceq
    #
    wb
    va
    vb
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    #
    @2
    @5
    @4
    @7
    @0
    cA
    @1
    crange
    breq1
    @10
    @3
    @6
    @1
    @0
    cA
    rneq
    eqeq2d
    bibi12d
    @1
    cB
    wceq
    @5
    @8
    @7
    @9
    @1
    cB
    cA
    crange
    breq2
    @1
    cB
    @6
    eqeq1
    bibi12d
    @0
    @1
    va
    vex
    vb
    vex
    brrange
    vtocl2g
end
