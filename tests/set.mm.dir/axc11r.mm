include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-12.mm"
include "sps.mm"
include "pm2.27.mm"
include "al2imi.mm"
include "syld.mm"

theorem axc11r
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y y = x -> ( A. x ph -> A. y ph ) )

  proof
    vy
    vx
    weq
    #
    vy
    wal
    wph
    vx
    wal
    #
    @0
    wph
    wi
    #
    vy
    wal
    #
    wph
    vy
    wal
    @0
    @1
    @3
    wi
    vy
    wph
    vy
    vx
    ax-12
    sps
    @0
    @2
    wph
    vy
    @0
    wph
    pm2.27
    al2imi
    syld
end
