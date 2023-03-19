include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "sbequ12r.mm"
include "equsal.mm"
include "bicomi.mm"

theorem sb6rf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb5rf.1: |- F/ y ph


  assert |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) )

  proof
    vy
    vx
    weq
    wph
    vx
    vy
    wsb
    #
    wi
    vy
    wal
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
    equsal
    bicomi
end
