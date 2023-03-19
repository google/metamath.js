include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "equtr.mm"
include "sbequ2.mm"
include "sbequ1.mm"
include "syl9.mm"
include "syld.mm"
include "wn.mm"
include "wal.mm"
include "ax13.mm"
include "sp.mm"
include "con3i.mm"
include "sb4.mm"
include "syl.mm"
include "equeuclr.mm"
include "imim1d.mm"
include "al2imi.mm"
include "sb2.mm"
include "syl6.mm"
include "pm2.61i.mm"

theorem sbequi
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) )

  proof
    vz
    vx
    weq
    #
    vx
    vy
    weq
    #
    wph
    vz
    vx
    wsb
    #
    wph
    vz
    vy
    wsb
    #
    wi
    #
    wi
    @0
    @1
    vz
    vy
    weq
    #
    @4
    vz
    vx
    vy
    equtr
    @0
    @2
    wph
    @5
    @3
    wph
    vz
    vx
    sbequ2
    wph
    vz
    vy
    sbequ1
    syl9
    syld
    @0
    wn
    #
    @1
    @1
    vz
    wal
    #
    @4
    vz
    vx
    vy
    ax13
    @6
    @2
    @0
    wph
    wi
    #
    vz
    wal
    #
    @7
    @3
    @6
    @0
    vz
    wal
    #
    wn
    @2
    @9
    wi
    @10
    @0
    @0
    vz
    sp
    con3i
    wph
    vz
    vx
    sb4
    syl
    @7
    @9
    @5
    wph
    wi
    #
    vz
    wal
    @3
    @1
    @8
    @11
    vz
    @1
    @5
    @0
    wph
    vx
    vz
    vy
    equeuclr
    imim1d
    al2imi
    wph
    vz
    vy
    sb2
    syl6
    syl9
    syld
    pm2.61i
end
