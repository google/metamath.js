include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-c11n.mm"
include "ax12.mm"
include "equcoms.mm"
include "sps-o.mm"
include "pm2.27.mm"
include "al2imi.mm"
include "sylsyld.mm"

theorem axc11-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> ( A. x ph -> A. y ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
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
    @1
    wph
    wi
    #
    vy
    wal
    #
    wph
    vy
    wal
    vx
    vy
    ax-c11n
    @0
    @2
    @4
    wi
    #
    vx
    @5
    vy
    vx
    wph
    vy
    vx
    ax12
    equcoms
    sps-o
    @1
    @3
    wph
    vy
    @1
    wph
    pm2.27
    al2imi
    sylsyld
end
