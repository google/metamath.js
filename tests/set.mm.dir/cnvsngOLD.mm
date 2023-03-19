include "cv.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "wceq.mm"
include "opeq1.mm"
include "sneqd.mm"
include "cnveqd.mm"
include "opeq2.mm"
include "eqeq12d.mm"
include "vex.mm"
include "cnvsn.mm"
include "vtocl2g.mm"

theorem cnvsngOLD
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> `' { <. A , B >. } = { <. B , A >. } )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    csn
    #
    ccnv
    #
    @1
    @0
    cop
    #
    csn
    #
    wceq
    cA
    @1
    cop
    #
    csn
    #
    ccnv
    #
    @1
    cA
    cop
    #
    csn
    #
    wceq
    cA
    cB
    cop
    #
    csn
    #
    ccnv
    #
    cB
    cA
    cop
    #
    csn
    #
    wceq
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
    @6
    @11
    @17
    @3
    @8
    @17
    @2
    @7
    @0
    cA
    @1
    opeq1
    sneqd
    cnveqd
    @17
    @5
    @10
    @0
    cA
    @1
    opeq2
    sneqd
    eqeq12d
    @1
    cB
    wceq
    #
    @9
    @14
    @11
    @16
    @18
    @8
    @13
    @18
    @7
    @12
    @1
    cB
    cA
    opeq2
    sneqd
    cnveqd
    @18
    @10
    @15
    @1
    cB
    cA
    opeq1
    sneqd
    eqeq12d
    @0
    @1
    vx
    vex
    vy
    vex
    cnvsn
    vtocl2g
end
