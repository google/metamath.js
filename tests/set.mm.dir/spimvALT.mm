include "nfv.mm"
include "spim.mm"

theorem spimvALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spimv.1: |- ( x = y -> ( ph -> ps ) )

  disjoint ps x
  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    spimv.1
    spim
end
