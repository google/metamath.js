include "cv.mm"
include "cdomain.mm"
include "wbr.mm"
include "cdm.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "dmeq.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "eqeq1.mm"
include "vex.mm"
include "brdomain.mm"
include "vtocl2g.mm"

theorem brdomaing
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> ( A Domain B <-> B = dom A ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    cdomain
    wbr
    #
    @1
    @0
    cdm
    #
    wceq
    #
    wb
    cA
    @1
    cdomain
    wbr
    #
    @1
    cA
    cdm
    #
    wceq
    #
    wb
    cA
    cB
    cdomain
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
    cdomain
    breq1
    @10
    @3
    @6
    @1
    @0
    cA
    dmeq
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
    cdomain
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
    brdomain
    vtocl2g
end
