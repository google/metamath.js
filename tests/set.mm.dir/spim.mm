include "weq.mm"
include "wi.mm"
include "ax6e.mm"
include "eximii.mm"
include "19.36i.mm"

theorem spim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spim.1: |- F/ x ps
  assume spim.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( A. x ph -> ps )

  proof
    wph
    wps
    vx
    spim.1
    vx
    vy
    weq
    wph
    wps
    wi
    vx
    vx
    vy
    ax6e
    spim.2
    eximii
    19.36i
end
