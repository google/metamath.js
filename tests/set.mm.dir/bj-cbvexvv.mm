include "nfv.mm"
include "cbvexv1.mm"

theorem bj-cbvexvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvalvv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
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
    bj-cbvalvv.1
    cbvexv1
end
