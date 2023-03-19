include "nfcv.mm"
include "cbvralf.mm"

theorem cbvral
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvral.1: |- F/ y ph
  assume cbvral.2: |- F/ x ps
  assume cbvral.3: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( A. x e. A ph <-> A. y e. A ps )

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
    cbvral.1
    cbvral.2
    cbvral.3
    cbvralf
end
