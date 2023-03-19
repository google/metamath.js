include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "wnf.mm"
include "bj-hbsb3t.mm"
include "axc4i.mm"
include "nf5.mm"
include "sylibr.mm"

theorem bj-nfs1t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> A. y ph ) -> F/ x [ y / x ] ph )

  proof
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
    #
    @1
    vx
    wal
    wi
    #
    vx
    wal
    @1
    vx
    wnf
    @0
    @2
    vx
    wph
    vx
    vy
    bj-hbsb3t
    axc4i
    @1
    vx
    nf5
    sylibr
end
