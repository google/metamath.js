include "wnf.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "nf5.mm"
include "biimpi.mm"
include "alimi.mm"
include "nfa2.mm"
include "bj-hbext.mm"
include "alrimi.mm"
include "syl.mm"
include "sylibr.mm"

theorem bj-nfext
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> F/ y E. x ph )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    @2
    vy
    wal
    wi
    #
    vy
    wal
    #
    @2
    vy
    wnf
    @1
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
    #
    @4
    @0
    @6
    vx
    @0
    @6
    wph
    vy
    nf5
    biimpi
    alimi
    @7
    @3
    vy
    @5
    vy
    vx
    nfa2
    wph
    vy
    vx
    bj-hbext
    alrimi
    syl
    @2
    vy
    nf5
    sylibr
end
