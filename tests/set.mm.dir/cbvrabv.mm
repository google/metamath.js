include "nfcv.mm"
include "nfv.mm"
include "cbvrab.mm"

theorem cbvrabv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvrabv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  assert |- { x e. A | ph } = { y e. A | ps }

  proof
    wph
    wps
    vx
    vy
    cA
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbvrabv.1
    cbvrab
end
