include "wa.mm"
include "wral.mm"
include "r19.26.mm"
include "ralbii.mm"
include "bitri.mm"

theorem r19.26-2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( A. x e. A A. y e. B ( ph /\ ps ) <-> ( A. x e. A A. y e. B ph /\ A. x e. A A. y e. B ps ) )

  proof
    wph
    wps
    wa
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
    wps
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wral
    @2
    vx
    cA
    wral
    wa
    @0
    @3
    vx
    cA
    wph
    wps
    vy
    cB
    r19.26
    ralbii
    @1
    @2
    vx
    cA
    r19.26
    bitri
end
