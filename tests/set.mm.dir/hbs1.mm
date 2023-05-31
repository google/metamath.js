include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wi.mm"
include "axc16.mm"
include "hbsb2.mm"
include "pm2.61i.mm"

theorem hbs1
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph -> A. x [ y / x ] ph )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    vx
    vy
    wsb
    #
    @0
    vx
    wal
    wi
    @0
    vx
    vy
    axc16
    wph
    vx
    vy
    hbsb2
    pm2.61i
end
