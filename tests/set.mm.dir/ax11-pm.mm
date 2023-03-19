include "wal.mm"
include "wi.mm"
include "2sp.mm"
include "gen2.mm"
include "nfa2.mm"
include "nfa1.mm"
include "2stdpc5.mm"
include "ax-mp.mm"

theorem ax11-pm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    #
    wph
    wi
    #
    vx
    wal
    vy
    wal
    @1
    wph
    vx
    wal
    vy
    wal
    wi
    @2
    vy
    vx
    wph
    vx
    vy
    2sp
    gen2
    @1
    wph
    vy
    vx
    wph
    vy
    vx
    nfa2
    @0
    vx
    nfa1
    2stdpc5
    ax-mp
end
