include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "crn.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "rnoprab.mm"
include "r2ex.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem rnoprab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ran { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } = { z | E. x e. A E. y e. B ph }

  proof
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    crn
    @0
    vy
    wex
    vx
    wex
    #
    vz
    cab
    wph
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    vz
    cab
    @0
    vx
    vy
    vz
    rnoprab
    @2
    @1
    vz
    wph
    vx
    vy
    cA
    cB
    r2ex
    abbii
    eqtr4i
end
