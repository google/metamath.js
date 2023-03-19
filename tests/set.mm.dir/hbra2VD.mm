include "wral.mm"
include "ralcom.mm"
include "hbra1.mm"
include "hbxfrbi.mm"

theorem hbra2VD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( A. x e. A A. y e. B ph -> A. y A. x e. A A. y e. B ph )

  proof
    wph
    vy
    cB
    wral
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    #
    vy
    cB
    wral
    vy
    wph
    vx
    vy
    cA
    cB
    ralcom
    @0
    vy
    cB
    hbra1
    hbxfrbi
end
