include "cv.mm"
include "csn.mm"
include "wf.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "sneq.mm"
include "feq2d.mm"
include "opeq1.mm"
include "sneqd.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "feq3d.mm"
include "opeq2.mm"
include "vex.mm"
include "fsn.mm"
include "vtocl2g.mm"

theorem fsng
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. C /\ B e. D ) -> ( F : { A } --> { B } <-> F = { <. A , B >. } ) )

  proof
    va
    cv
    #
    csn
    #
    vb
    cv
    #
    csn
    #
    cF
    wf
    #
    cF
    @0
    @2
    cop
    #
    csn
    #
    wceq
    #
    wb
    cA
    csn
    #
    @3
    cF
    wf
    #
    cF
    cA
    @2
    cop
    #
    csn
    #
    wceq
    #
    wb
    @8
    cB
    csn
    #
    cF
    wf
    #
    cF
    cA
    cB
    cop
    #
    csn
    #
    wceq
    #
    wb
    va
    vb
    cA
    cB
    cC
    cD
    @0
    cA
    wceq
    #
    @4
    @9
    @7
    @12
    @18
    @1
    @8
    @3
    cF
    @0
    cA
    sneq
    feq2d
    @18
    @6
    @11
    cF
    @18
    @5
    @10
    @0
    cA
    @2
    opeq1
    sneqd
    eqeq2d
    bibi12d
    @2
    cB
    wceq
    #
    @9
    @14
    @12
    @17
    @19
    @3
    @13
    cF
    @8
    @2
    cB
    sneq
    feq3d
    @19
    @11
    @16
    cF
    @19
    @10
    @15
    @2
    cB
    cA
    opeq2
    sneqd
    eqeq2d
    bibi12d
    @0
    @2
    cF
    va
    vex
    vb
    vex
    fsn
    vtocl2g
end
