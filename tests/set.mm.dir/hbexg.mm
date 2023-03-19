include "wal.mm"
include "wi.mm"
include "wex.mm"
include "nfa2.mm"
include "wnf.mm"
include "sp.mm"
include "alimi.mm"
include "nf5.mm"
include "sylibr.mm"
include "nfexd.mm"
include "sylib.mm"
include "alrimi.mm"
include "alcom.mm"

theorem hbexg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph -> A. x ph ) -> A. x A. y ( E. y ph -> A. x E. y ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wph
    vy
    wex
    #
    @3
    vx
    wal
    wi
    #
    vx
    wal
    #
    vy
    wal
    @4
    vy
    wal
    vx
    wal
    @2
    @5
    vy
    @0
    vy
    vx
    nfa2
    #
    @2
    @3
    vx
    wnf
    @5
    @2
    wph
    vx
    vy
    @6
    @2
    @0
    vx
    wal
    wph
    vx
    wnf
    @1
    @0
    vx
    @0
    vy
    sp
    alimi
    wph
    vx
    nf5
    sylibr
    nfexd
    @3
    vx
    nf5
    sylib
    alrimi
    @4
    vy
    vx
    alcom
    sylib
end
