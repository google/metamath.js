include "weq.mm"
include "wsb.mm"
include "wa.mm"
include "wex.mm"
include "sbequ12r.mm"
include "equsex.mm"
include "bicomi.mm"

theorem sb5rf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb5rf.1: |- F/ y ph


  assert |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) )

  proof
    vy
    vx
    weq
    wph
    vx
    vy
    wsb
    #
    wa
    vy
    wex
    wph
    @0
    wph
    vy
    vx
    sb5rf.1
    wph
    vy
    vx
    sbequ12r
    equsex
    bicomi
end
