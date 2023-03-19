include "wal.mm"
include "wn.mm"
include "ax-11.mm"
include "con3i.mm"
include "alimi.mm"
include "ax-c7.mm"
include "syl.mm"

theorem axc711
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x -. A. y A. x ph -> A. y ph )

  proof
    wph
    vx
    wal
    vy
    wal
    #
    wn
    #
    vx
    wal
    #
    wn
    wph
    vy
    wal
    #
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    wn
    @3
    @6
    @2
    @5
    @1
    vx
    @0
    @4
    wph
    vy
    vx
    ax-11
    con3i
    alimi
    con3i
    @3
    vx
    ax-c7
    syl
end
