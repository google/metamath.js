include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rexbidv2.mm"

theorem rexss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> ( E. x e. A ph <-> E. x e. B ( x e. A /\ ph ) ) )

  proof
    cA
    cB
    wss
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cA
    cB
    @0
    @3
    @1
    cB
    wcel
    #
    @2
    wa
    #
    wph
    wa
    @4
    @3
    wa
    @0
    @2
    @5
    wph
    @0
    @2
    @4
    cA
    cB
    @1
    ssel
    pm4.71rd
    anbi1d
    @4
    @2
    wph
    anass
    syl6bb
    rexbidv2
end
