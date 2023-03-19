include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "cdm.mm"
include "wex.mm"
include "copab.mm"
include "cxp.mm"
include "dmoprab.mm"
include "19.42v.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstri.mm"

theorem dmoprabss
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- dom { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B )

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
    #
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    cdm
    @1
    vz
    wex
    #
    vx
    vy
    copab
    #
    cA
    cB
    cxp
    #
    @1
    vx
    vy
    vz
    dmoprab
    @3
    @0
    wph
    vz
    wex
    #
    wa
    #
    vx
    vy
    copab
    @4
    @2
    @6
    vx
    vy
    @0
    wph
    vz
    19.42v
    opabbii
    @5
    vx
    vy
    cA
    cB
    opabssxp
    eqsstri
    eqsstri
end
