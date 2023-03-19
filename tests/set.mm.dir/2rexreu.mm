include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "wrmo.mm"
include "reurmo.mm"
include "reurex.mm"
include "rmoimi.mm"
include "syl.mm"
include "2reurex.mm"
include "anim12ci.mm"
include "reu5.mm"
include "sylibr.mm"

theorem 2rexreu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A y
  disjoint x y
  disjoint B x
  disjoint k x
  assert |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) -> E! x e. A E! y e. B ph )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    vy
    cB
    wreu
    #
    wa
    wph
    vy
    cB
    wreu
    #
    vx
    cA
    wrex
    #
    @3
    vx
    cA
    wrmo
    #
    wa
    @3
    vx
    cA
    wreu
    @1
    @5
    @2
    @4
    @1
    @0
    vx
    cA
    wrmo
    @5
    @0
    vx
    cA
    reurmo
    @3
    @0
    vx
    cA
    wph
    vy
    cB
    reurex
    rmoimi
    syl
    wph
    vy
    vx
    cB
    cA
    2reurex
    anim12ci
    @3
    vx
    cA
    reu5
    sylibr
end
