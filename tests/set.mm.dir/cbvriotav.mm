include "nfv.mm"
include "cbvriota.mm"

theorem cbvriotav
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvriotav.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  assert |- ( iota_ x e. A ph ) = ( iota_ y e. A ps )

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
    cbvriotav.1
    cbvriota
end
