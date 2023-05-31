include "wn.mm"
include "ax-5.mm"
include "spimw.mm"

theorem spimvw
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume spimvw.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ps x
  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    vy
    wps
    wn
    vx
    ax-5
    spimvw.1
    spimw
end
