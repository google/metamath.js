include "wal.mm"
include "wn.mm"
include "axc711toc7.mm"
include "con4i.mm"
include "axc711.mm"
include "alimi.mm"
include "syl.mm"

theorem axc711to11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    vx
    wal
    #
    @0
    wn
    #
    vy
    wal
    wn
    #
    vy
    wal
    #
    wph
    vx
    wal
    #
    vy
    wal
    @3
    @0
    @1
    vy
    axc711toc7
    con4i
    @2
    @4
    vy
    wph
    vy
    vx
    axc711
    alimi
    syl
end
