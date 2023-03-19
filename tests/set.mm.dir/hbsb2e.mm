include "wsb.mm"
include "weq.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "sb4e.mm"
include "sb2.mm"
include "axc4i.mm"
include "syl.mm"

theorem hbsb2e
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph )

  proof
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    wph
    vy
    wex
    #
    wi
    #
    vx
    wal
    @0
    vx
    vy
    wsb
    #
    vx
    wal
    wph
    vx
    vy
    sb4e
    @1
    @2
    vx
    @0
    vx
    vy
    sb2
    axc4i
    syl
end
