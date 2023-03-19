include "nfv.mm"
include "cbvex.mm"

theorem cbvexvOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- ( E. x ph <-> E. y ps )

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
    cbvex
end
