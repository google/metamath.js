include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax12v2.mm"
include "sps.mm"
include "pm2.27.mm"
include "al2imi.mm"
include "syld.mm"
include "spsd.mm"

theorem axc11rvOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> ( A. y ph -> A. x ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wph
    wph
    vx
    wal
    #
    vy
    @1
    wph
    @0
    wph
    wi
    #
    vx
    wal
    #
    @2
    @0
    wph
    @4
    wi
    vx
    wph
    vx
    vy
    ax12v2
    sps
    @0
    @3
    wph
    vx
    @0
    wph
    pm2.27
    al2imi
    syld
    spsd
end
