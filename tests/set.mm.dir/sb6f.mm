include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nf5ri.mm"
include "sbimi.mm"
include "sb4a.mm"
include "syl.mm"
include "sb2.mm"
include "impbii.mm"

theorem sb6f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb6f.1: |- F/ y ph


  assert |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    wph
    wi
    vx
    wal
    #
    @0
    wph
    vy
    wal
    #
    vx
    vy
    wsb
    @1
    wph
    @2
    vx
    vy
    wph
    vy
    sb6f.1
    nf5ri
    sbimi
    wph
    vx
    vy
    sb4a
    syl
    wph
    vx
    vy
    sb2
    impbii
end
