include "wn.mm"
include "ax-5.mm"
include "spimw.mm"

theorem spimvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
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
