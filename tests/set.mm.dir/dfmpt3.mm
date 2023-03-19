include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "df-mpt.mm"
include "cop.mm"
include "wex.mm"
include "velsn.mm"
include "anbi2i.mm"
include "2exbii.mm"
include "eliunxp.mm"
include "elopab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "eqtr4i.mm"

theorem dfmpt3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z


  assert |- ( x e. A |-> B ) = U_ x e. A ( { x } X. { B } )

  proof
    vx
    cA
    cB
    cmpt
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    @0
    csn
    cB
    csn
    #
    cxp
    ciun
    #
    vx
    vy
    cA
    cB
    df-mpt
    vz
    @7
    @5
    vz
    cv
    #
    @0
    @2
    cop
    wceq
    #
    @1
    @2
    @6
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    @9
    @4
    wa
    #
    vy
    wex
    vx
    wex
    @8
    @7
    wcel
    @8
    @5
    wcel
    @12
    @13
    vx
    vy
    @11
    @4
    @9
    @10
    @3
    @1
    vy
    cB
    velsn
    anbi2i
    anbi2i
    2exbii
    vx
    vy
    cA
    @6
    @8
    eliunxp
    @4
    vx
    vy
    @8
    elopab
    3bitr4i
    eqriv
    eqtr4i
end
