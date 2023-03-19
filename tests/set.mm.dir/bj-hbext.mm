include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "nfa2.mm"
include "hbnt.mm"
include "alimi.mm"
include "bj-hbalt.mm"
include "syl.mm"
include "alrimi.mm"
include "df-ex.mm"
include "bicomi.mm"
include "albii.mm"
include "3imtr3g.mm"

theorem bj-hbext
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. y A. x ( ph -> A. x ph ) -> ( E. y ph -> A. x E. y ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    wph
    wn
    #
    vy
    wal
    #
    wn
    #
    @5
    vx
    wal
    #
    wph
    vy
    wex
    #
    @7
    vx
    wal
    @2
    @4
    @4
    vx
    wal
    wi
    #
    vx
    wal
    @5
    @6
    wi
    @2
    @8
    vx
    @0
    vx
    vy
    nfa2
    @2
    @3
    @3
    vx
    wal
    wi
    #
    vy
    wal
    @8
    @1
    @9
    vy
    wph
    vx
    hbnt
    alimi
    @3
    vx
    vy
    bj-hbalt
    syl
    alrimi
    @4
    vx
    hbnt
    syl
    @7
    @5
    wph
    vy
    df-ex
    bicomi
    #
    @5
    @7
    vx
    @10
    albii
    3imtr3g
end
