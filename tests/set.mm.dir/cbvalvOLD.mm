include "nfv.mm"
include "cbval.mm"

theorem cbvalvOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- ( A. x ph <-> A. y ps )

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbvalv.1
    cbval
end
