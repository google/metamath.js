include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wsb.mm"
include "equs5.mm"
include "sb2.mm"
include "syl6bi.mm"

theorem sb3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    @0
    wph
    wa
    vx
    wex
    @0
    wph
    wi
    vx
    wal
    wph
    vx
    vy
    wsb
    wph
    vx
    vy
    equs5
    wph
    vx
    vy
    sb2
    syl6bi
end
