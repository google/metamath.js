include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cdm.mm"
include "wex.mm"
include "cab.mm"
include "dmopab.mm"
include "19.42v.mm"
include "abbii.mm"
include "ssab2.mm"
include "eqsstri.mm"

theorem dmopabss
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- dom { <. x , y >. | ( x e. A /\ ph ) } C_ A

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    cdm
    @1
    vy
    wex
    #
    vx
    cab
    #
    cA
    @1
    vx
    vy
    dmopab
    @3
    @0
    wph
    vy
    wex
    #
    wa
    #
    vx
    cab
    cA
    @2
    @5
    vx
    @0
    wph
    vy
    19.42v
    abbii
    @4
    vx
    cA
    ssab2
    eqsstri
    eqsstri
end
