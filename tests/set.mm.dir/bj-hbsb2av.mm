include "wal.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "sb4a.mm"
include "bj-sb2v.mm"
include "axc4i.mm"
include "syl.mm"

theorem bj-hbsb2av
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph )

  proof
    wph
    vy
    wal
    vx
    vy
    wsb
    vx
    vy
    weq
    wph
    wi
    #
    vx
    wal
    wph
    vx
    vy
    wsb
    #
    vx
    wal
    wph
    vx
    vy
    sb4a
    @0
    @1
    vx
    wph
    vx
    vy
    bj-sb2v
    axc4i
    syl
end
