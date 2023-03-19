include "cv.mm"
include "csn.mm"
include "cop.mm"
include "wf1o.mm"
include "wceq.mm"
include "wb.mm"
include "sneq.mm"
include "f1oeq2.mm"
include "syl.mm"
include "opeq1.mm"
include "sneqd.mm"
include "f1oeq1.mm"
include "bitrd.mm"
include "f1oeq3.mm"
include "opeq2.mm"
include "vex.mm"
include "f1osn.mm"
include "vtocl2g.mm"

theorem f1osng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> { <. A , B >. } : { A } -1-1-onto-> { B } )

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
    @0
    @2
    cop
    #
    csn
    #
    wf1o
    #
    cA
    csn
    #
    @3
    cA
    @2
    cop
    #
    csn
    #
    wf1o
    #
    @7
    cB
    csn
    #
    cA
    cB
    cop
    #
    csn
    #
    wf1o
    #
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
    @6
    @7
    @3
    @5
    wf1o
    #
    @10
    @15
    @1
    @7
    wceq
    @6
    @16
    wb
    @0
    cA
    sneq
    @1
    @7
    @3
    @5
    f1oeq2
    syl
    @15
    @5
    @9
    wceq
    @16
    @10
    wb
    @15
    @4
    @8
    @0
    cA
    @2
    opeq1
    sneqd
    @7
    @3
    @5
    @9
    f1oeq1
    syl
    bitrd
    @2
    cB
    wceq
    #
    @10
    @7
    @11
    @9
    wf1o
    #
    @14
    @17
    @3
    @11
    wceq
    @10
    @18
    wb
    @2
    cB
    sneq
    @3
    @11
    @7
    @9
    f1oeq3
    syl
    @17
    @9
    @13
    wceq
    @18
    @14
    wb
    @17
    @8
    @12
    @2
    cB
    cA
    opeq2
    sneqd
    @7
    @11
    @9
    @13
    f1oeq1
    syl
    bitrd
    @0
    @2
    va
    vex
    vb
    vex
    f1osn
    vtocl2g
end
