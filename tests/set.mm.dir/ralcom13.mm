include "wral.mm"
include "ralcom.mm"
include "ralbii.mm"
include "3bitri.mm"

theorem ralcom13
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint C y
  assert |- ( A. x e. A A. y e. B A. z e. C ph <-> A. z e. C A. y e. B A. x e. A ph )

  proof
    wph
    vz
    cC
    wral
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @0
    vx
    cA
    wral
    #
    vy
    cB
    wral
    wph
    vx
    cA
    wral
    #
    vz
    cC
    wral
    #
    vy
    cB
    wral
    @2
    vy
    cB
    wral
    vz
    cC
    wral
    @0
    vx
    vy
    cA
    cB
    ralcom
    @1
    @3
    vy
    cB
    wph
    vx
    vz
    cA
    cC
    ralcom
    ralbii
    @2
    vy
    vz
    cB
    cC
    ralcom
    3bitri
end
