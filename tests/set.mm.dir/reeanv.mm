include "nfv.mm"
include "reean.mm"

theorem reeanv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint ph y
  disjoint ps x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) )

  proof
    wph
    wps
    vx
    vy
    cA
    cB
    wph
    vy
    nfv
    wps
    vx
    nfv
    reean
end
