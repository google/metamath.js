include "nfv.mm"
include "cbviota.mm"

theorem cbviotav
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbviotav.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- ( iota x ph ) = ( iota y ps )

  proof
    wph
    wps
    vx
    vy
    cbviotav.1
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbviota
end
