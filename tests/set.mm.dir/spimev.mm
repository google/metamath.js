include "nfv.mm"
include "spime.mm"

theorem spimev
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spimev.1: |- ( x = y -> ( ph -> ps ) )

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
    spimev.1
    spime
end
