include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "copab.mm"
include "df-mpt.mm"
include "rneqi.mm"
include "rnopab.mm"
include "eqtri.mm"
include "df-rex.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem rnmptsn
  let vx: setvar x
  let vu: setvar u
  let cA: class A

  disjoint A u
  disjoint u x
  assert |- ran ( x e. A |-> { x } ) = { u | E. x e. A u = { x } }

  proof
    vx
    cA
    vx
    cv
    #
    csn
    #
    cmpt
    #
    crn
    #
    @0
    cA
    wcel
    vu
    cv
    @1
    wceq
    #
    wa
    #
    vx
    wex
    #
    vu
    cab
    #
    @4
    vx
    cA
    wrex
    #
    vu
    cab
    @3
    @5
    vx
    vu
    copab
    #
    crn
    @7
    @2
    @9
    vx
    vu
    cA
    @1
    df-mpt
    rneqi
    @5
    vx
    vu
    rnopab
    eqtri
    @8
    @6
    vu
    @4
    vx
    cA
    df-rex
    abbii
    eqtr4i
end
