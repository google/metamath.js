include "wreu.mm"
include "wrex.mm"
include "reurex.mm"
include "reximi.mm"
include "syl.mm"

theorem 2reu2rex
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
  assert |- ( E! x e. A E! y e. B ph -> E. x e. A E. y e. B ph )

  proof
    wph
    vy
    cB
    wreu
    #
    vx
    cA
    wreu
    @0
    vx
    cA
    wrex
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @0
    vx
    cA
    reurex
    @0
    @1
    vx
    cA
    wph
    vy
    cB
    reurex
    reximi
    syl
end
