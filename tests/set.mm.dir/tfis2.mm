include "nfv.mm"
include "tfis2f.mm"

theorem tfis2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume tfis2.1: |- ( x = y -> ( ph <-> ps ) )
  assume tfis2.2: |- ( x e. On -> ( A. y e. x ps -> ph ) )

  disjoint ps x
  disjoint ph y
  disjoint x y
  assert |- ( x e. On -> ph )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    tfis2.1
    tfis2.2
    tfis2f
end
