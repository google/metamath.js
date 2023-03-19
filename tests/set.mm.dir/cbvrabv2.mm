include "nfcv.mm"
include "nfv.mm"
include "cbvrabcsf.mm"

theorem cbvrabv2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cbvrabv2.1: |- ( x = y -> A = B )
  assume cbvrabv2.2: |- ( x = y -> ( ph <-> ps ) )

  disjoint A y
  disjoint B x
  disjoint ph y
  disjoint ps x
  assert |- { x e. A | ph } = { y e. B | ps }

  proof
    wph
    wps
    vx
    vy
    cA
    cB
    vy
    cA
    nfcv
    vx
    cB
    nfcv
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbvrabv2.1
    cbvrabv2.2
    cbvrabcsf
end
