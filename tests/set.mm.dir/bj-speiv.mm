include "weq.mm"
include "ax6ev.mm"
include "mpbiri.mm"
include "eximii.mm"

theorem bj-speiv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-speiv.1: |- ( x = y -> ( ph <-> ps ) )
  assume bj-speiv.2: |- ps

  disjoint x y
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
    @0
    wph
    wps
    bj-speiv.2
    bj-speiv.1
    mpbiri
    eximii
end
