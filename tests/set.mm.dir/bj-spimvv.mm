include "weq.mm"
include "wi.mm"
include "ax6ev.mm"
include "eximii.mm"
include "19.36iv.mm"

theorem bj-spimvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-spimvv.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ps x
  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    vx
    vy
    weq
    wph
    wps
    wi
    vx
    vx
    vy
    ax6ev
    bj-spimvv.1
    eximii
    19.36iv
end
