include "weq.mm"
include "ax6ev.mm"
include "a1i.mm"
include "eximii.mm"

theorem exiftru
  param wph: wff ph
  param vx: setvar x
  let vy: setvar y
  assume exiftru.1: |- ph


  assert |- E. x ph

  proof
    vx
    vy
    weq
    #
    wph
    vx
    vx
    vy
    ax6ev
    wph
    @0
    exiftru.1
    a1i
    eximii
end
