include "weq.mm"
include "wal.mm"
include "wa.mm"
include "wi.mm"
include "nfa1.mm"
include "ax-12.mm"
include "imp.mm"
include "exlimi.mm"

theorem equs5aALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    vy
    wal
    #
    wa
    @0
    wph
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
    @1
    @3
    wph
    vx
    vy
    ax-12
    imp
    exlimi
end
