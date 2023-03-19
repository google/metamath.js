include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "nf5r.mm"
include "alimi.mm"
include "bj-nfs1t.mm"
include "syl.mm"

theorem bj-nfs1t2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> F/ x [ y / x ] ph )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    wph
    wph
    vy
    wal
    wi
    #
    vx
    wal
    wph
    vx
    vy
    wsb
    vx
    wnf
    @0
    @1
    vx
    wph
    vy
    nf5r
    alimi
    wph
    vx
    vy
    bj-nfs1t
    syl
end
