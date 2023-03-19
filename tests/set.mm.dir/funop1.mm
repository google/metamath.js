include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wfun.mm"
include "csn.mm"
include "wb.mm"
include "wa.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "cbvex2v.mm"
include "vex.mm"
include "funopsn.mm"
include "sneqd.mm"
include "spc2ev.mm"
include "adantl.mm"
include "exlimiv.mm"
include "syl.mm"
include "expcom.mm"
include "funsn.mm"
include "funeq.mm"
include "mpbiri.mm"
include "exlimivv.mm"
include "impbid1.mm"
include "sylbi.mm"

theorem funop1
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vv: setvar v
  let vw: setvar w
  let vk: setvar k

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint F a
  disjoint F v
  disjoint F w
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint k x
  assert |- ( E. x E. y F = <. x , y >. -> ( Fun F <-> E. x E. y F = { <. x , y >. } ) )

  proof
    cF
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
    wex
    vx
    wex
    cF
    vv
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    vw
    wex
    vv
    wex
    cF
    wfun
    #
    cF
    @2
    csn
    #
    wceq
    #
    vy
    wex
    vx
    wex
    #
    wb
    #
    @3
    @7
    vx
    vy
    vv
    vw
    @0
    @4
    wceq
    @1
    @5
    wceq
    wa
    @2
    @6
    cF
    @0
    @1
    @4
    @5
    opeq12
    eqeq2d
    cbvex2v
    @7
    @12
    vv
    vw
    @7
    @8
    @11
    @8
    @7
    @11
    @8
    @7
    wa
    @4
    va
    cv
    #
    csn
    wceq
    #
    cF
    @13
    @13
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    va
    wex
    @11
    cF
    @4
    @5
    va
    vv
    vex
    vw
    vex
    funopsn
    @18
    @11
    va
    @17
    @11
    @14
    @10
    @17
    vx
    vy
    @13
    @13
    va
    vex
    #
    @19
    @0
    @13
    wceq
    @1
    @13
    wceq
    wa
    #
    @9
    @16
    cF
    @20
    @2
    @15
    @0
    @1
    @13
    @13
    opeq12
    sneqd
    eqeq2d
    spc2ev
    adantl
    exlimiv
    syl
    expcom
    @10
    @8
    vx
    vy
    @10
    @8
    @9
    wfun
    @0
    @1
    vx
    vex
    vy
    vex
    funsn
    cF
    @9
    funeq
    mpbiri
    exlimivv
    impbid1
    exlimivv
    sylbi
end
