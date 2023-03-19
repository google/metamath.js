include "wa.mm"
include "wrex.mm"
include "r19.41v.mm"
include "rexbii.mm"
include "bitri.mm"

theorem r19.41vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint ps x
  disjoint ps y
  assert |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A E. y e. B ph /\ ps ) )

  proof
    wph
    wps
    wa
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wph
    vy
    cB
    wrex
    #
    wps
    wa
    #
    vx
    cA
    wrex
    @1
    vx
    cA
    wrex
    wps
    wa
    @0
    @2
    vx
    cA
    wph
    wps
    vy
    cB
    r19.41v
    rexbii
    @1
    wps
    vx
    cA
    r19.41v
    bitri
end
