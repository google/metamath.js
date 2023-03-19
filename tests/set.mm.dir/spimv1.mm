include "weq.mm"
include "wi.mm"
include "ax6ev.mm"
include "eximii.mm"
include "19.36i.mm"

theorem spimv1
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume spimv1.nf: |- F/ x ps
  assume spimv1.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    spimv1.nf
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
    spimv1.1
    eximii
    19.36i
end
