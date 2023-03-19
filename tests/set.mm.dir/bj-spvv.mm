include "weq.mm"
include "biimpd.mm"
include "bj-spimvv.mm"

theorem bj-spvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-spvv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
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
    bj-spvv.1
    biimpd
    bj-spimvv
end
