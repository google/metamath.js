include "wsb.mm"
include "wal.mm"
include "stdpc4.mm"
include "sbid2.mm"
include "sylib.mm"

theorem sbtrt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbtrt.nf: |- F/ y ph


  assert |- ( A. y [ y / x ] ph -> ph )

  proof
    wph
    vx
    vy
    wsb
    #
    vy
    wal
    @0
    vy
    vx
    wsb
    wph
    @0
    vy
    vx
    stdpc4
    wph
    vy
    vx
    sbtrt.nf
    sbid2
    sylib
end
