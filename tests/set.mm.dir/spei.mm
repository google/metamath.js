include "weq.mm"
include "ax6e.mm"
include "mpbiri.mm"
include "eximii.mm"

theorem spei
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spei.1: |- ( x = y -> ( ph <-> ps ) )
  assume spei.2: |- ps


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
    ax6e
    @0
    wph
    wps
    spei.2
    spei.1
    mpbiri
    eximii
end
