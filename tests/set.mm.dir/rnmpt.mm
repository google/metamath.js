include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "rnopab.mm"
include "cmpt.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "rneqi.mm"
include "df-rex.mm"
include "abbii.mm"
include "3eqtr4i.mm"

theorem rnmpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  let cC: class C
  assume rnmpt.1: |- F = ( x e. A |-> B )

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint x z
  disjoint C x
  disjoint C y
  disjoint C z
  assert |- ran F = { y | E. x e. A y = B }

  proof
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    crn
    @1
    vx
    wex
    #
    vy
    cab
    cF
    crn
    @0
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    vx
    vy
    rnopab
    cF
    @2
    cF
    vx
    cA
    cB
    cmpt
    @2
    rnmpt.1
    vx
    vy
    cA
    cB
    df-mpt
    eqtri
    rneqi
    @4
    @3
    vy
    @0
    vx
    cA
    df-rex
    abbii
    3eqtr4i
end
