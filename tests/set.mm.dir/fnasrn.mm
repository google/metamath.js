include "cmpt.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "ciun.mm"
include "crn.mm"
include "dfmpt.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "wceq.mm"
include "eqid.mm"
include "rnmpt.mm"
include "velsn.mm"
include "rexbii.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "df-iun.mm"

theorem fnasrn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume dfmpt.1: |- B e. _V


  assert |- ( x e. A |-> B ) = ran ( x e. A |-> <. x , B >. )

  proof
    vx
    cA
    cB
    cmpt
    vx
    cA
    vx
    cv
    cB
    cop
    #
    csn
    #
    ciun
    #
    vx
    cA
    @0
    cmpt
    #
    crn
    #
    vx
    cA
    cB
    dfmpt.1
    dfmpt
    @4
    vy
    cv
    #
    @1
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    @2
    @4
    @5
    @0
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @8
    vx
    vy
    cA
    @0
    @3
    @3
    eqid
    rnmpt
    @7
    @10
    vy
    @6
    @9
    vx
    cA
    vy
    @0
    velsn
    rexbii
    abbii
    eqtr4i
    vx
    vy
    cA
    @1
    df-iun
    eqtr4i
    eqtr4i
end
