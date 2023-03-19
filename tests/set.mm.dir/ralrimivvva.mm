include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "3anassrs.mm"
include "ralrimiva.mm"

theorem ralrimivvva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralrimivvva.1: |- ( ( ph /\ ( x e. A /\ y e. B /\ z e. C ) ) -> ps )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  assert |- ( ph -> A. x e. A A. y e. B A. z e. C ps )

  proof
    wph
    wps
    vz
    cC
    wral
    #
    vy
    cB
    wral
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @0
    vy
    cB
    @2
    vy
    cv
    cB
    wcel
    #
    wa
    wps
    vz
    cC
    wph
    @1
    @3
    vz
    cv
    cC
    wcel
    wps
    ralrimivvva.1
    3anassrs
    ralrimiva
    ralrimiva
    ralrimiva
end
