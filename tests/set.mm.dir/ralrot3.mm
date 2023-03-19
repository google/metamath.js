include "wral.mm"
include "ralcom.mm"
include "ralbii.mm"
include "bitri.mm"

theorem ralrot3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A z
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint y z
  assert |- ( A. x e. A A. y e. B A. z e. C ph <-> A. z e. C A. x e. A A. y e. B ph )

  proof
    wph
    vz
    cC
    wral
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wph
    vy
    cB
    wral
    #
    vz
    cC
    wral
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wral
    vz
    cC
    wral
    @0
    @2
    vx
    cA
    wph
    vy
    vz
    cB
    cC
    ralcom
    ralbii
    @1
    vx
    vz
    cA
    cC
    ralcom
    bitri
end
