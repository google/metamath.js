include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "bj-hbalt.mm"
include "alimi.mm"
include "alcoms.mm"
include "nf5.mm"
include "albii.mm"
include "3imtr4i.mm"

theorem bj-nfalt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> F/ y A. x ph )

  proof
    wph
    wph
    vy
    wal
    wi
    #
    vy
    wal
    #
    vx
    wal
    wph
    vx
    wal
    #
    @2
    vy
    wal
    wi
    #
    vy
    wal
    #
    wph
    vy
    wnf
    #
    vx
    wal
    @2
    vy
    wnf
    @0
    @4
    vy
    vx
    @0
    vx
    wal
    @3
    vy
    wph
    vy
    vx
    bj-hbalt
    alimi
    alcoms
    @5
    @1
    vx
    wph
    vy
    nf5
    albii
    @2
    vy
    nf5
    3imtr4i
end
