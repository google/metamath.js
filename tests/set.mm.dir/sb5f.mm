include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "sb6f.mm"
include "equs45f.mm"
include "bitr4i.mm"

theorem sb5f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb6f.1: |- F/ y ph


  assert |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) )

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
    wi
    vx
    wal
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    vy
    sb6f.1
    sb6f
    wph
    vx
    vy
    sb6f.1
    equs45f
    bitr4i
end
