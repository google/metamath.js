include "wal.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "ax6e.mm"
include "biimpd.mm"
include "eximii.mm"
include "19.35i.mm"
include "19.9d.mm"
include "syl5.mm"

theorem spd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume spd.1: |- ( ch -> F/ x ps )
  assume spd.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( ch -> ( A. x ph -> ps ) )

  proof
    wph
    vx
    wal
    wps
    vx
    wex
    wch
    wps
    wph
    wps
    vx
    vx
    vy
    weq
    #
    wph
    wps
    wi
    vx
    vx
    vy
    ax6e
    @0
    wph
    wps
    spd.2
    biimpd
    eximii
    19.35i
    wps
    wch
    vx
    spd.1
    19.9d
    syl5
end
