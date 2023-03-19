include "wex.mm"
include "wn.mm"
include "weq.mm"
include "weu.mm"
include "wal.mm"
include "nfeu1.mm"
include "nfa1.mm"
include "wi.mm"
include "exists1.mm"
include "axc16.mm"
include "sylbi.mm"
include "exlimd.mm"
include "com12.mm"
include "alex.mm"
include "syl6ib.mm"
include "con2d.mm"
include "imp.mm"

theorem exists2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x )

  proof
    wph
    vx
    wex
    #
    wph
    wn
    vx
    wex
    #
    vx
    vx
    weq
    #
    vx
    weu
    #
    wn
    @0
    @3
    @1
    @0
    @3
    wph
    vx
    wal
    #
    @1
    wn
    @3
    @0
    @4
    @3
    wph
    @4
    vx
    @2
    vx
    nfeu1
    wph
    vx
    nfa1
    @3
    vx
    vy
    weq
    vx
    wal
    wph
    @4
    wi
    vx
    vy
    exists1
    wph
    vx
    vy
    axc16
    sylbi
    exlimd
    com12
    wph
    vx
    alex
    syl6ib
    con2d
    imp
end
