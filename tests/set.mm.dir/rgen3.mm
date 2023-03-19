include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "rgen2.mm"

theorem rgen3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume rgen3.1: |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint x y
  disjoint x z
  assert |- A. x e. A A. y e. B A. z e. C ph

  proof
    wph
    vz
    cC
    wral
    vx
    vy
    cA
    cB
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    wph
    vz
    cC
    @0
    @1
    vz
    cv
    cC
    wcel
    wph
    rgen3.1
    3expa
    ralrimiva
    rgen2
end
