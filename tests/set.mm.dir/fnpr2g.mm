include "cv.mm"
include "cpr.mm"
include "wfn.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "preq1.mm"
include "fneq2d.mm"
include "id.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "preq1d.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "preq2.mm"
include "preq2d.mm"
include "vex.mm"
include "fnprb.mm"
include "vtocl2g.mm"

theorem fnpr2g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> ( F Fn { A , B } <-> F = { <. A , ( F ` A ) >. , <. B , ( F ` B ) >. } ) )

  proof
    cF
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wfn
    #
    cF
    @0
    @0
    cF
    cfv
    #
    cop
    #
    @1
    @1
    cF
    cfv
    #
    cop
    #
    cpr
    #
    wceq
    #
    wb
    cF
    cA
    @1
    cpr
    #
    wfn
    #
    cF
    cA
    cA
    cF
    cfv
    #
    cop
    #
    @7
    cpr
    #
    wceq
    #
    wb
    cF
    cA
    cB
    cpr
    #
    wfn
    #
    cF
    @13
    cB
    cB
    cF
    cfv
    #
    cop
    #
    cpr
    #
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
    @3
    @11
    @9
    @15
    @22
    @2
    @10
    cF
    @0
    cA
    @1
    preq1
    fneq2d
    @22
    @8
    @14
    cF
    @22
    @5
    @13
    @7
    @22
    @0
    cA
    @4
    @12
    @22
    id
    @0
    cA
    cF
    fveq2
    opeq12d
    preq1d
    eqeq2d
    bibi12d
    @1
    cB
    wceq
    #
    @11
    @17
    @15
    @21
    @23
    @10
    @16
    cF
    @1
    cB
    cA
    preq2
    fneq2d
    @23
    @14
    @20
    cF
    @23
    @7
    @19
    @13
    @23
    @1
    cB
    @6
    @18
    @23
    id
    @1
    cB
    cF
    fveq2
    opeq12d
    preq2d
    eqeq2d
    bibi12d
    @0
    @1
    cF
    va
    vex
    vb
    vex
    fnprb
    vtocl2g
end
