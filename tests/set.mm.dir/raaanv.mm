include "nfv.mm"
include "raaan.mm"

theorem raaanv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint ph y
  disjoint ps x
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) )

  proof
    wph
    wps
    vx
    vy
    cA
    wph
    vy
    nfv
    wps
    vx
    nfv
    raaan
end
