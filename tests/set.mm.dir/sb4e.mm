include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "sb1.mm"
include "equs5e.mm"
include "syl.mm"

theorem sb4e
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) )

  proof
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wa
    vx
    wex
    @0
    wph
    vy
    wex
    wi
    vx
    wal
    wph
    vx
    vy
    sb1
    wph
    vx
    vy
    equs5e
    syl
end
