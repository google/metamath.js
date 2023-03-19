include "nfv.mm"
include "bj-spimev.mm"

theorem bj-spimevv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-spimevv.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ph x
  assert |- ( ph -> E. x ps )

  proof
    wph
    wps
    vx
    vy
    wph
    vx
    nfv
    bj-spimevv.1
    bj-spimev
end
