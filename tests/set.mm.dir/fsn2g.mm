include "cv.mm"
include "csn.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "sneq.mm"
include "feq2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "eqidd.mm"
include "id.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "vex.mm"
include "fsn2.mm"
include "vtoclg.mm"

theorem fsn2g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b


  assert |- ( A e. V -> ( F : { A } --> B <-> ( ( F ` A ) e. B /\ F = { <. A , ( F ` A ) >. } ) ) )

  proof
    va
    cv
    #
    csn
    #
    cB
    cF
    wf
    #
    @0
    cF
    cfv
    #
    cB
    wcel
    #
    cF
    @0
    @3
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    wb
    cA
    csn
    #
    cB
    cF
    wf
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    cF
    cA
    @11
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    wb
    va
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @10
    @8
    @16
    @17
    @1
    @9
    cB
    cF
    @0
    cA
    sneq
    feq2d
    @17
    @4
    @12
    @7
    @15
    @17
    @3
    @11
    cB
    @0
    cA
    cF
    fveq2
    #
    eleq1d
    @17
    cF
    cF
    @6
    @14
    @17
    cF
    eqidd
    @17
    @5
    @13
    @17
    @0
    cA
    @3
    @11
    @17
    id
    @18
    opeq12d
    sneqd
    eqeq12d
    anbi12d
    bibi12d
    @0
    cB
    cF
    va
    vex
    fsn2
    vtoclg
end
