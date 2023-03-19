include "weq.mm"
include "biimpd.mm"
include "spimv.mm"

theorem spv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ps x
  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    spv.1
    biimpd
    spimv
end
