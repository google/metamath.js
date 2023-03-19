include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "wa.mm"
include "reu5.mm"
include "rexbii.mm"
include "rmobii.mm"
include "anbi12i.mm"
include "bitri.mm"

theorem 2reu5a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k


  assert |- ( E! x e. A E! y e. B ph <-> ( E. x e. A ( E. y e. B ph /\ E* y e. B ph ) /\ E* x e. A ( E. y e. B ph /\ E* y e. B ph ) ) )

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
    #
    @0
    vx
    cA
    wrmo
    #
    wa
    wph
    vy
    cB
    wrex
    wph
    vy
    cB
    wrmo
    wa
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
    @0
    vx
    cA
    reu5
    @1
    @4
    @2
    @5
    @0
    @3
    vx
    cA
    wph
    vy
    cB
    reu5
    #
    rexbii
    @0
    @3
    vx
    cA
    @6
    rmobii
    anbi12i
    bitri
end
