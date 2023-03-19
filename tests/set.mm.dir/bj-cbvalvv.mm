include "nfv.mm"
include "cbvalv1.mm"

theorem bj-cbvalvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvalvv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
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
    bj-cbvalvv.1
    cbvalv1
end
