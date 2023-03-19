include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "opeq1.mm"
include "sneqd.mm"
include "id.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "opeq2.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "fvsn.mm"
include "vtocl2g.mm"

theorem fvsng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> ( { <. A , B >. } ` A ) = B )

  proof
    va
    cv
    #
    @0
    vb
    cv
    #
    cop
    #
    csn
    #
    cfv
    #
    @1
    wceq
    cA
    cA
    @1
    cop
    #
    csn
    #
    cfv
    #
    @1
    wceq
    cA
    cA
    cB
    cop
    #
    csn
    #
    cfv
    #
    cB
    wceq
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
    @4
    @7
    @1
    @11
    @0
    cA
    @3
    @6
    @11
    @2
    @5
    @0
    cA
    @1
    opeq1
    sneqd
    @11
    id
    fveq12d
    eqeq1d
    @1
    cB
    wceq
    #
    @7
    @10
    @1
    cB
    @12
    cA
    @6
    @9
    @12
    @5
    @8
    @1
    cB
    cA
    opeq2
    sneqd
    fveq1d
    @12
    id
    eqeq12d
    @0
    @1
    va
    vex
    vb
    vex
    fvsn
    vtocl2g
end
