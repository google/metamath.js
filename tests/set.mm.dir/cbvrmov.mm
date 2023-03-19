include "nfv.mm"
include "cbvrmo.mm"

theorem cbvrmov
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvralv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  assert |- ( E* x e. A ph <-> E* y e. A ps )

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
    cbvralv.1
    cbvrmo
end
