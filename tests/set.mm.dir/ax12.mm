include "weq.mm"
include "wal.mm"
include "wi.mm"
include "axc11r.mm"
include "ala1.mm"
include "syl6.mm"
include "a1d.mm"
include "wn.mm"
include "sp.mm"
include "axc15.mm"
include "syl7.mm"
include "pm2.61i.mm"

theorem ax12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    wph
    vy
    wal
    #
    @0
    wph
    wi
    vx
    wal
    #
    wi
    #
    wi
    @1
    @4
    @0
    @1
    @2
    wph
    vx
    wal
    @3
    wph
    vy
    vx
    axc11r
    wph
    @0
    vx
    ala1
    syl6
    a1d
    @2
    wph
    @1
    wn
    @0
    @3
    wph
    vy
    sp
    wph
    vx
    vy
    axc15
    syl7
    pm2.61i
end
