include "wal.mm"
include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "sb1.mm"
include "equs5a.mm"
include "syl.mm"

theorem sb4a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) )

  proof
    wph
    vy
    wal
    #
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    @0
    wa
    vx
    wex
    @1
    wph
    wi
    vx
    wal
    @0
    vx
    vy
    sb1
    wph
    vx
    vy
    equs5a
    syl
end
