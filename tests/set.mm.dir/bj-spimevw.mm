include "ax-5.mm"
include "spimeh.mm"

theorem bj-spimevw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-spimevw.1: |- ( x = y -> ( ph -> ps ) )

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
    ax-5
    bj-spimevw.1
    spimeh
end
