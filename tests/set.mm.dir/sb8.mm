include "wsb.mm"
include "nfs1.mm"
include "sbequ12.mm"
include "cbval.mm"

theorem sb8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb5rf.1: |- F/ y ph


  assert |- ( A. x ph <-> A. y [ y / x ] ph )

  proof
    wph
    wph
    vx
    vy
    wsb
    vx
    vy
    sb5rf.1
    wph
    vx
    vy
    sb5rf.1
    nfs1
    wph
    vx
    vy
    sbequ12
    cbval
end
