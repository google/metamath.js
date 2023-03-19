include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "vex.mm"
include "opth1.mm"
include "exlimiv.mm"
include "opeq1.mm"
include "opeq2.mm"
include "eqeq1d.mm"
include "spcegv.mm"
include "syl5.mm"
include "impbid2.mm"
include "eldm2.mm"
include "opex.mm"
include "elsn.mm"
include "exbii.mm"
include "bitri.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem dmsnopg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> dom { <. A , B >. } = { A } )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    cB
    cop
    #
    csn
    #
    cdm
    #
    cA
    csn
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @1
    wceq
    #
    vy
    wex
    #
    @5
    cA
    wceq
    #
    @5
    @3
    wcel
    #
    @5
    @4
    wcel
    @0
    @9
    @10
    @8
    @10
    vy
    @5
    @6
    cA
    cB
    vx
    vex
    #
    vy
    vex
    opth1
    exlimiv
    @10
    @5
    cB
    cop
    #
    @1
    wceq
    #
    @0
    @9
    @5
    cA
    cB
    opeq1
    @8
    @14
    vy
    cB
    cV
    @6
    cB
    wceq
    @7
    @13
    @1
    @6
    cB
    @5
    opeq2
    eqeq1d
    spcegv
    syl5
    impbid2
    @11
    @7
    @2
    wcel
    #
    vy
    wex
    @9
    vy
    @5
    @2
    @12
    eldm2
    @15
    @8
    vy
    @7
    @1
    @5
    @6
    opex
    elsn
    exbii
    bitri
    vx
    cA
    velsn
    3bitr4g
    eqrdv
end
