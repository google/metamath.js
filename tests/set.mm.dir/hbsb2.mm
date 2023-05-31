include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wi.mm"
include "sb4.mm"
include "sb2.mm"
include "axc4i.mm"
include "syl6.mm"

theorem hbsb2
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    wph
    vx
    vy
    wsb
    #
    @0
    wph
    wi
    #
    vx
    wal
    @1
    vx
    wal
    wph
    vx
    vy
    sb4
    @2
    @1
    vx
    wph
    vx
    vy
    sb2
    axc4i
    syl6
end
