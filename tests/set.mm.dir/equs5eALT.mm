include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "nfa1.mm"
include "hbe1.mm"
include "19.23bi.mm"
include "ax-12.mm"
include "syl5.mm"
include "imp.mm"
include "exlimi.mm"

theorem equs5eALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wa
    @0
    wph
    vy
    wex
    #
    wi
    #
    vx
    wal
    #
    vx
    @2
    vx
    nfa1
    @0
    wph
    @3
    wph
    @1
    vy
    wal
    #
    @0
    @3
    wph
    @4
    vy
    wph
    vy
    hbe1
    19.23bi
    @1
    vx
    vy
    ax-12
    syl5
    imp
    exlimi
end
